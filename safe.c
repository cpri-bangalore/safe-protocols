/*
safe.c - Table-driven Safe Protocol Subset Filters.

==== Copyright (c) 2026 Central Power Research Institute, Bangalore ====

	Smart Grid Research Laboratory, CPRI
	sgrl [HYPHEN] cpri [AT] cpri [DOT] in

	This version of safe.c/safe.h is not free software; and can
	only be used for evaluation, research, and educational purposes.

========================================================================

All filter decisions are driven by const lookup tables:

	- Whitelist arrays:
		TABLE[v] == 1 means accept

	- Field transitions:
		TABLE[state][tag]		-> next state

	- DNP3 point size:
		POINT_SIZE[group][variation]	-> bytes

ACSL annotations enable Frama-C/WP verification:
	frama-c -wp -wp-rte -wp-timeout 90 -wp-prover alt-ergo,z3 safe.c
*/

#include "safe.h"

/* --- BER length decoder (shared by ASN, GOOSE, and MMS) ------------------- */

/*@

requires // that buffer is readable
	\valid_read(buffer + (0 .. buffer_length - 1));

requires // that the offset pointer is valid
	\valid(offset);

requires // that the offset pointer does not alias the buffer
	\separated(offset, buffer + (0 .. buffer_length - 1));

requires // that the offset starts within bounds
	*offset	<= buffer_length;

requires
	buffer_length <= 65535;

assigns // only the offset
	*offset;

ensures	// that offset never exceeds buffer length
	*offset <= buffer_length;

ensures	// that offset never moves backward
	*offset >= \old(*offset);
*/
static U32 read_length (
	const	u8	*const	buffer,
	const	u32		buffer_length,
		u32	*const	offset
)
{
	/*@ ghost u32 offset_init = *offset;*/

	/* overflowed == 1 marks a malformed length encoding (no length octet,
	 * indefinite 0x80, over-long length-of-length, non-minimal long form,
	 * truncation, or value overflow). overflowed == 0 marks a well-formed
	 * length whose value is in .value (which may legitimately be 0). */

	U32 out = {
		.value		= 0U,
		.overflowed	= 0,
		.underflowed	= 0
	};

	if (*offset >= buffer_length) {		/* no length octet present	*/
		out.overflowed = 1;
		return out;
	}

	const u8 first_byte = buffer[(*offset)++];

	/*@
		assert
			*offset >= offset_init;
	*/

	/* Short form: first byte is the length (0..127; length 0 is legitimate) */
	if ((first_byte & BER_LONG_FORM_BIT) == 0U) {
		out.value = (u32) first_byte;
		return out;
	}

	/* Long form */

	if (*offset >= buffer_length) {		/* not enough bytes		*/
		out.overflowed = 1;
		return out;
	}

	const u32 num_length_bytes = (u32) (first_byte & BER_LENGTH_MASK);

	/* Reject indefinite length (0x80) and over-long length-of-length */
	if (num_length_bytes == 0 || num_length_bytes > ASN_MAX_LENGTH_BYTES) {
		out.overflowed = 1;
		return out;
	}

	/* Reject leading zero bytes (non-minimal long form) */
	if (num_length_bytes > 1U && buffer[*offset] == 0x00U) {
		out.overflowed = 1;
		return out;
	}

	const U32 Bytes_Required = ADD(*offset, num_length_bytes);

	if (Bytes_Required.overflowed || Bytes_Required.value > buffer_length) {
		out.overflowed = 1;
		return out;
	}

	u32 length = 0U;

	/*@
		loop invariant
				0 <= i <= num_length_bytes;

		loop invariant
				*offset <= buffer_length;
		loop invariant
				*offset >= offset_init;

		loop assigns
				i,
				length,
				*offset,
				out;

		loop variant
				num_length_bytes - i;
	*/
	for (
		u32 i = 0U;
		(i < num_length_bytes) && (*offset < buffer_length);
		++i
	)
	{
		if (length > (UINT32_MAX >> 8U)) /* would overflow */
		{
			out.overflowed = 1;
			return out;
		}

		length = (length << 8U) | (u32) buffer[(*offset)++];
	}

	/*@ assert *offset >= offset_init; */

	/* Reject non-minimal long form for small values */
	if (num_length_bytes > 1U && length < 128U) {
		out.overflowed = 1;
		return out;
	}

	out.value = length;
	return out;
}

/* ==========================================================
 * SafeASN.1 - whitelist array + recursive TLV walker
 * ========================================================== */

/*
=== Flags for asn_filter_top / asn_filter_recursive. ===

ASN_FLAG_ALLOW_ZERO_PRIMITIVE:
	Permit primitive context-specific tags with length == 0.
	MMS legitimately uses these for IMPLICIT NULL choices
	(e.g. ObjectScope::vmdSpecific [0] IMPLICIT NULL = 80 00).
	Must NOT be set for GOOSE/SV or standalone ASN.1 where
	zero-length implicit fields indicate IEDFuRL-class vulnerabilities.

ASN_FLAG_ALLOW_CONTEXT:
	Permit context-specific tags 0x80-0xBF.
	MMS service bodies use these for CHOICE/IMPLICIT encodings.
	NOT set by safe_asn_filter (strict IEC 61850 / standalone mode);
	set by safe_mms_filter body validator and safe_asn_filter_relaxed.
*/

#define ASN_FLAG_ALLOW_ZERO_PRIMITIVE	(1U)
#define ASN_FLAG_ALLOW_CONTEXT		(2U)

#define ASN_TAG_WHITELIST_SIZE		(192U)

static const u8 ASN_TAG_WHITELIST [ASN_TAG_WHITELIST_SIZE] = {

	[0x01] = 1, /* BOOLEAN				*/
	[0x02] = 1, /* INTEGER				*/
	[0x03] = 1, /* BIT STRING			*/
	[0x04] = 1, /* OCTET STRING			*/
	[0x05] = 1, /* NULL				*/
	[0x06] = 1, /* OBJECT IDENTIFIER		*/

	[0x0C] = 1, /* UTF8String			*/

	[0x16] = 1, /* IA5String			*/

#ifdef SAFE_ENABLE_ASN_VISIBLE_STRING
	[0x1A] = 1, /* VisibleString (MMS filenames,
			object references)		*/
#endif

	[0x30] = 1, /* SEQUENCE				*/

	/*
	* Application 0x40-0x7F and context-specific 0x80-0xBF: NOT in whitelist.
	* Application tags (LDAP, SNMP, Kerberos) are not used in IEC 61850.
	* Both ranges are allowed as a single contiguous block (0x40-0xBF) in
	* asn_filter_recursive_relaxed / safe_asn_filter_relaxed for substation
	* PKI (X.509/Kerberos) traffic.
	*
	* Context-specific tags are additionally gated by ASN_FLAG_ALLOW_CONTEXT
	* in asn_filter_recursive / asn_parse_recursive for MMS body parsing.
	* safe_asn_filter (strict) rejects the entire 0x40-0xBF range.
	* safe_mms_filter body
	* validator and safe_asn_filter_relaxed set ASN_FLAG_ALLOW_CONTEXT.
	*/
};

/* Tags accepted by safe_asn_filter_relaxed but not by safe_asn_filter (strict).
 * Used in X.509/OCSP/Kerberos/LDAP traffic; not present in IEC 61850. */
static const u8 ASN_TAG_WHITELIST_RELAXED [ASN_TAG_WHITELIST_SIZE] = {
	[0x0A] = 1, /* ENUMERATED	(OCSP response status)		*/
	[0x13] = 1, /* PrintableString	(X.509 DNs)			*/
	[0x17] = 1, /* UTCTime		(X.509 validity dates ≤ 2049)	*/
	[0x18] = 1, /* GeneralizedTime	(X.509 validity dates > 2049)	*/
	[0x1B] = 1, /* GeneralString	(Kerberos)			*/
	[0x31] = 1, /* SET		(X.509 DNs / multi-valued attrs)	*/
};

/*@

requires // that data length is limited
	length <= 65535;

requires // that the buffer is empty or readable
	length == 0 ||
	\valid_read(data + (0 .. length - 1));

assigns
	\nothing;

ensures // that result is valid(1) OR invalid(0)
	\result == 0 || \result == 1;
*/
SAFE_PURE static inline u32 is_valid_printable_string (
	const u8	*const	data,
	const u32		length
)
{
	if (length > SAFE_ASN_MAX_PRINTABLE_STRING) {
		return 0U; /* too long */
	}

	/*@
		loop invariant
			0 <= i <= length;

		loop assigns
			i;

		loop variant
			length - i;
	*/
	for (u32 i = 0U; i < length; i++)
	{
		const u8 byte = data[i];

		/* PrintableString: A-Z a-z 0-9 space '()+,-./:=? */
		if (
			(byte >= 'A' && byte <= 'Z') ||
			(byte >= 'a' && byte <= 'z') ||
			(byte >= '0' && byte <= '9') ||
			byte == ' ' || byte == '\'' || byte == '(' || byte == ')' ||
			byte == '+' || byte == ','  || byte == '-' || byte == '.' ||
			byte == '/' || byte == ':'  || byte == '=' || byte == '?'
		)
		{
			continue;
		}

		return 0U; /* invalid character */
	}

	return 1U; /* valid */
}


/*@

requires // that data length is limited
	length <= 65535;

requires // that the buffer is empty or readable
	length == 0 ||
	\valid_read(data + (0 .. length - 1));

assigns
	\nothing;

ensures // 1 = valid, 0 = invalid
	\result == 0 || \result == 1;
*/
SAFE_PURE static inline u32 is_valid_IA5string (
	const u8	*const	data,
	const u32		length
)
{
	if (length > SAFE_ASN_MAX_IA5_STRING) {
		return 0U; /* too long */
	}

	/*@
		loop invariant
			0 <= i <= length;

		loop assigns
			i;

		loop variant
			length - i;
	*/
	for (u32 i = 0U; i < length; i++)
	{
		if (data[i] > 0x7FU) {	/* > 127 */
			return 0U;	/* invalid */
		}
	}

	return 1U; /* valid */
}

#ifdef SAFE_ENABLE_ASN_VISIBLE_STRING

/*@

requires // that data length is limited
	length <= 65535;

requires // that the buffer is empty or readable
	length == 0 ||
	\valid_read(data + (0 .. length - 1));

assigns
	\nothing;

ensures // 1 = valid, 0 = invalid
	\result == 0 || \result == 1;
*/
SAFE_PURE static inline u32 is_valid_visible_string (
	const u8	*const	data,
	const u32		length
)
{
	if (length > SAFE_ASN_MAX_VISIBLE_STRING) {
		return 0U; /* too long */
	}

	/*@
		loop invariant
			0 <= i <= length;

		loop assigns
			i;

		loop variant
			length - i;
	*/
	for (u32 i = 0U; i < length; i++)
	{
		const u8 byte = data[i];

		/* VisibleString: printable ASCII 0x20 (space) to 0x7E (tilde).
		 * Excludes control chars (< 0x20) and DEL (0x7F) and high bytes. */
		if (byte < 0x20U || byte > 0x7EU) {
			return 0U; /* invalid character */
		}
	}

	return 1U; /* valid */
}
#endif /* SAFE_ENABLE_ASN_VISIBLE_STRING */

/* --- Taint predicates ----------------------------------------
 * Each predicate defines what "sanitized" means for a given
 * input element. Frama-C/WP proves these hold after the
 * corresponding validation code, ensuring no tainted value
 * reaches a sensitive operation (array index, pointer
 * arithmetic, or protocol decision).
 * ------------------------------------------------------------ */

/*@

// ASN.1: tag byte passed whitelist check

predicate is_sanitized_tag(u8 t) =
	t < ASN_TAG_WHITELIST_SIZE && ASN_TAG_WHITELIST[t] != 0;

// ASN.1: length value passed bounds checks

predicate is_sanitized_length(u32 len, u32 offset, u32 e) =
	len <= SAFE_ASN_MAX_MESSAGE && offset + len <= e;

// ASN.1: BOOLEAN content is valid (1 byte, canonical DER value)

predicate is_sanitized_boolean{L}(u8 *buf, u32 offset) =
	buf[offset] == 0x00 || buf[offset] == 0x01 || buf[offset] == 0xFF;

// ASN.1: INTEGER content is non-empty and minimally encoded

predicate is_sanitized_integer{L}(u8 *buf, u32 offset, u32 len) =
	len > 0 &&
	(
		len <= 1 ||
		!(
			(
				 buf[offset  ] == 0x00 &&
				(buf[offset+1] & 0x80) == 0
			) ||
			(
				buf[offset   ] == 0xFF &&
				(buf[offset+1] & 0x80) != 0
			)
		)
	);

// ASN.1: VisibleString size bounded and printable ASCII only

predicate is_sanitized_visible_string(u32 len) =
	len <= SAFE_ASN_MAX_VISIBLE_STRING;

// ASN.1: BIT STRING unused bits valid and size bounded

predicate is_sanitized_bitstring{L}(u8 *buf, u32 offset, u32 len) =
	len <= SAFE_ASN_MAX_BIT_STRING &&
	(len == 0 || (buf[offset] <= 7 && (len > 1 || buf[offset] == 0)));

// ASN.1: OCTET STRING size bounded

predicate is_sanitized_octetstring(u32 len) =
	len <= SAFE_ASN_MAX_OCTET_STRING;

// ASN.1: OID is non-empty and size bounded

predicate is_sanitized_oid(u32 len) =
	len > 0 && len <= SAFE_ASN_MAX_OID;

*/

/* asn_filter_recursive -- the STRICT IEC 61850 TLV walker, and the base for three
 * near-identical recursive walkers. When changing shared tag/length/recursion
 * logic, update all three to keep them in sync:
 *   - asn_filter_recursive (this): IEC 61850 profile -- whitelisted tags only,
 *       INTEGER restricted to 1/2/4/8-byte widths, OCTET/BIT/OID/string size caps,
 *       context tags (0x80-0xBF) admitted only under ASN_FLAG_ALLOW_CONTEXT.
 *   - asn_filter_recursive_relaxed: non-IEC / PKI profile -- additionally admits
 *       SET, PrintableString, GeneralizedTime/GeneralString and drops the IEC
 *       size/width restrictions; no flags parameter (always relaxed).
 *   - asn_parse_recursive: same validation as this walker, but also records each
 *       TLV (tag, length, content pointer, depth) into nodes[] (zero-copy parser).
 */

/*@

requires // that buffer is readable
	\valid_read(buffer + (0 .. buffer_length - 1));

requires // that walk region is within the buffer
	offset <= end <= buffer_length;

requires // that buffer size is limited
	buffer_length	<= 65535;

requires // that recursion depth is bounded
	depth		<= max_depth;

requires // that max_depth is within the configured upper bound
	max_depth	<= SAFE_ASN_MMS_BODY_MAX_DEPTH;

requires // that node_count pointer is writable
	\valid(node_count);

requires // that node_count starts within bounds
	*node_count <= SAFE_ASN_MAX_NODES;

decreases // the walk region on each call (Termination)
	end - offset;

assigns // node_count
	*node_count;

ensures // node_count remains bounded
	*node_count <= SAFE_ASN_MAX_NODES;

ensures // node_count never decreases
	*node_count >= \old(*node_count);

*/
static SafeAsnResult asn_filter_recursive (
	const	u8	*const	buffer,
	const	u32		buffer_length,
		u32		offset,
	const	u32		end,
	const	u32		depth,
	const	u32		max_depth,
		u32	*const	node_count,
	const	u32		flags
)
{
	/*@ ghost u32 offset_entry	= offset;	*/
	/*@ ghost u32 nc_entry		= *node_count;	*/

	/*@
		loop invariant
				offset	<= end;

		loop invariant
				end	<= buffer_length;

		loop invariant
				offset >= offset_entry;

		loop invariant
				*node_count <= SAFE_ASN_MAX_NODES;

		loop invariant
				*node_count >= nc_entry;

		loop assigns
				offset,
				*node_count;

		loop variant
				end - offset;
	*/
	while (offset < end)
	{
		if (*node_count >= SAFE_ASN_MAX_NODES) {
			return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
		}

		++(*node_count);

		/*@ ghost u32 offset_top = offset; */

		/* Tag: whitelist check (context tags 0x80-0xBF gated by ASN_FLAG_ALLOW_CONTEXT) */

		/*@ assert offset < end <= buffer_length; */

		const u8 tag = buffer[offset++];

		if (
			(
				tag >= ASN_TAG_WHITELIST_SIZE		||
				! ASN_TAG_WHITELIST[tag]
			)
			&&
			! (
				(flags & ASN_FLAG_ALLOW_CONTEXT)	&&
				tag	>= 0x80U			&&
				tag	< ASN_TAG_WHITELIST_SIZE
			)
		) {
			return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
		}

		/*@ assert tag < 192;			*/
		/*@ assert is_sanitized_tag(tag) ||
			((flags & ASN_FLAG_ALLOW_CONTEXT) != 0U && tag >= 0x80U);	*/

		/* Multi-byte tag (context high-tag): skip up to 3 continuation bytes	*/

		/*@ assert offset > offset_top;		*/

		if ((tag & BER_HIGH_TAG_MASK) == BER_HIGH_TAG_MASK)
		{
			u32 continuation_bytes = 0U;

			/*@
				loop invariant
						offset <= buffer_length;

				loop invariant
						offset > offset_top;

				loop invariant
						0 <= continuation_bytes <= SAFE_MAX_CONTINUATION_BYTES;

				loop assigns
						offset,
						continuation_bytes;

				loop variant
						(int)(SAFE_MAX_CONTINUATION_BYTES - continuation_bytes);
			*/
			while (
				offset			< buffer_length &&
				continuation_bytes	< SAFE_MAX_CONTINUATION_BYTES
			)
			{
				const u8 byte = buffer[offset++];

				++continuation_bytes;

				if ((byte & BER_CONTINUATION_BIT) == 0U) {
					break;
				}
			}

			/* Unterminated high-tag: reject */
			if (continuation_bytes >= SAFE_MAX_CONTINUATION_BYTES) {
				return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
			}

			/* Tag header must not extend past current TLV boundary */
			if (offset > end) {
				return_asn(ASN_REJECT_TRUNCATE, PREVIOUS(offset));
			}
		}

		/*@ assert offset > offset_top; */
		/*@ assert offset <= end;	*/

		/* Length */
		if (offset >= buffer_length) {
			return_asn(ASN_REJECT_TRUNCATE, offset);
		}

		/*@ assert offset < buffer_length; */

		const u8 length_byte = buffer[offset++];

		if (length_byte == BER_INDEFINITE_LENGTH)
		{
			const u32 off = PREVIOUS(offset);
			return_asn(ASN_REJECT_INDEF, off);
		}

		u32 length = 0U;

		if ((length_byte & BER_LONG_FORM_BIT) == 0U)
		{
			length = (u32)length_byte;
		}
		else
		{
			const u32 num_length_bytes = (u32) (
						length_byte & BER_LENGTH_MASK
			);

			if (num_length_bytes > ASN_MAX_LENGTH_BYTES) {
				return_asn(ASN_REJECT_LENGTH, offset);
			}

			const U32 Bytes_Required = ADD(offset, num_length_bytes);

			if (Bytes_Required.overflowed || Bytes_Required.value > buffer_length) {
				return_asn(ASN_REJECT_TRUNCATE, offset);
			}

			/*@
				loop invariant
						0 <= i <= num_length_bytes;

				loop invariant
						offset <= buffer_length;
				loop invariant
						offset > offset_top;

				loop assigns
						i,
						length,
						offset;

				loop variant
						num_length_bytes - i;
			*/
			for
			(
				u32 i = 0U;
				(
					(i	< num_length_bytes	) &&
					(offset < buffer_length		)
				);
				++i
			)
			{
				if (length > (UINT32_MAX >> 8U)) { /* would overflow */
					return_asn(ASN_REJECT_LENGTH, offset);
				}

				length = (length << 8U) | (u32)buffer[offset++];
			}
		}

		/* Length header must not extend past current TLV boundary */
		if (offset > end) {
			return_asn(ASN_REJECT_TRUNCATE, PREVIOUS(offset));
		}

		/*@ assert offset > offset_top; */
		/*@ assert offset <= end; */

		if (length > SAFE_ASN_MAX_MESSAGE) {
			return_asn(ASN_REJECT_SIZE, offset);
		}

		const U32 Remaining = SUBTRACT(end, offset);

		if (Remaining.underflowed || length > end || length > Remaining.value) {
			return_asn(ASN_REJECT_TRUNCATE, offset);
		}

		/*@ assert offset + length <= end;		*/
		/*@ assert offset + length <= buffer_length;	*/

		/*@ assert tag < ASN_TAG_WHITELIST_SIZE;				*/

		/*@ assert is_sanitized_tag(tag) ||
			((flags & ASN_FLAG_ALLOW_CONTEXT) != 0U && tag >= 0x80U);	*/

		/*@ assert is_sanitized_length(length, offset, end);			*/

		switch (tag)
		{
			case ASN_TAG_BOOLEAN: /* BOOLEAN: 1 byte */
			{
				if (length != 1U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (
					buffer[offset] != 0x00U &&	/* false	*/
					buffer[offset] != 0x01U &&	/* BER true	*/
					buffer[offset] != 0xFFU		/* DER true	*/
				)
				{
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_NULL:
			{
				if (length != 0U) { /* NULL must be 0 bytes */
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_INTEGER:	/* INTEGER: machine-word width + minimal encoding */
			case ASN_TAG_ENUMERATED:/* same encoding rules as INTEGER */
			{
				/* SafeASN.1 profile: restrict to machine-word widths.
				 * IEC 61850 and MMS integer fields are always 1, 2, 4,
				 * or 8 bytes; 3-byte and 5-7 byte encodings do not occur
				 * in conformant messages and are a common fuzzer target. */
				if (length != 1U && length != 2U && length != 4U && length != 8U) {
					return_asn(ASN_REJECT_BADINT, offset);
				}

				/* Non-minimal encoding check (BER S8.3.2 / DER S11.5):
				 * leading 0x00 on a positive integer or 0xFF on a
				 * negative integer means the value fits in fewer bytes. */
				if (length != 1U)
				{
					const U32 Next = ADD(offset, 1U);

					if (Next.overflowed) {
						return_asn(ASN_REJECT_TRUNCATE, offset);
					}

					const u8 b_and_sign = buffer[Next.value] & BER_SIGN_BIT;

					if (buffer[offset] == 0x00U && b_and_sign == 0U) {
						return_asn(ASN_REJECT_BADINT, offset);
					}

					if (buffer[offset] == 0xFFU && b_and_sign != 0U) {
						return_asn(ASN_REJECT_BADINT, offset);
					}
				}

				break;
			}

			case ASN_TAG_UTF8_STRING: /* UTF8String (MMS mMSString / Unicode): size bounded */
			{
				if (length > SAFE_ASN_MAX_UTF8_STRING) {
					return_asn(ASN_REJECT_SIZE, offset);
				}

				break;
			}

			case ASN_TAG_OCTET_STRING: /* OCTET STRING: size bounded */
			{
				if (length > SAFE_ASN_MAX_OCTET_STRING) {
					return_asn(ASN_REJECT_SIZE, offset);
				}

				break;
			}

			case ASN_TAG_BITSTRING: /* BIT STRING: unused bits 0-7, size bounded */
			{
				if (length > SAFE_ASN_MAX_BIT_STRING) {
					return_asn(ASN_REJECT_SIZE, offset);
				}

				if (length > 0 && buffer[offset] > 7U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (length == 1U && buffer[offset] != 0U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_OID:
			{
				if (length == 0U) { /* OID: must not be empty */
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (length > SAFE_ASN_MAX_OID) { /* OID: size bounded */
					return_asn(ASN_REJECT_SIZE, offset);
				}

				break;
			}

			case ASN_TAG_IA5_STRING:
			{
				/*@ assert length == 0 || \valid_read(buffer + offset + (0 .. length - 1)); */
				if (! is_valid_IA5string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

#ifdef SAFE_ENABLE_ASN_VISIBLE_STRING
			case ASN_TAG_VISIBLE_STRING:
			{
				/*@ assert length == 0 || \valid_read(buffer + offset + (0 .. length - 1)); */
				if (! is_valid_visible_string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}
#endif

			/* Taint: all content checks passed for this TLV */

			/*@
				assert tag == ASN_TAG_BOOLEAN
					==> is_sanitized_boolean(buffer, offset);
			*/

			/*@
				assert tag == ASN_TAG_INTEGER
					==> is_sanitized_integer(buffer, offset, length);
			*/

			/*@
				assert tag == ASN_TAG_OCTET_STRING
					==> is_sanitized_octetstring(length);
			*/

			/*@
				assert tag == ASN_TAG_BITSTRING
					==> is_sanitized_bitstring(buffer, offset, length);
			*/

			/*@
				assert tag == ASN_TAG_OID
					==> is_sanitized_oid(length);
			*/

			/*@
				assert tag == ASN_TAG_VISIBLE_STRING
					==> is_sanitized_visible_string(length);
			*/

			case ASN_TAG_SEQUENCE: /* SEQUENCE: recurse into children */
			{
				if (depth >= max_depth) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				if (*node_count >= SAFE_ASN_MAX_NODES) {
					return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
				}

				const U32 Child_End = ADD(offset, length);

				if (Child_End.overflowed) {
					return_asn(ASN_REJECT_TRUNCATE, offset);
				}

				const U32 Next_Depth = ADD(1U, depth);

				if (Next_Depth.overflowed) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				/*@ assert Child_End.value <= buffer_length; */
				const SafeAsnResult child_result = asn_filter_recursive (
									buffer,
									buffer_length,
									offset,
									Child_End.value,
									Next_Depth.value,
									max_depth,
									node_count,
									flags
				);

				if (child_result.error != ASN_OK) {
					return child_result;
				}

				break;
			}

			default: /* constructed context-specific / application tags: recurse */
			{
				if ((tag & 0x20U) != 0U)	/* constructed bit set */
				{
					if (depth >= max_depth) {
						return_asn(ASN_REJECT_DEPTH, offset);
					}

					if (*node_count >= SAFE_ASN_MAX_NODES) {
						return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
					}

					const U32 Child_End = ADD(offset, length);

					if (Child_End.overflowed) {
						return_asn(ASN_REJECT_TRUNCATE, offset);
					}

					const U32 Next_Depth = ADD(1U, depth);

					if (Next_Depth.overflowed) {
						return_asn(ASN_REJECT_DEPTH, offset);
					}

					/*@ assert Child_End.value <= buffer_length; */
					const SafeAsnResult child_result = asn_filter_recursive (
										buffer,
										buffer_length,
										offset,
										Child_End.value,
										Next_Depth.value,
										max_depth,
										node_count,
										flags
					);

					if (child_result.error != ASN_OK) {
						return child_result;
					}
				}
				/*
				* Primitive context-specific / application tag.
				* These encode IMPLICIT-typed fields (INTEGER, BOOLEAN,
				* ENUMERATED, ---); a zero-length encoding is a BER grammar
				* violation for all such types - except IMPLICIT NULL, which
				* legitimately encodes as T 00 (e.g. MMS ObjectScope::vmdSpecific
				* [0] IMPLICIT NULL = 80 00). Only allowed when the caller sets
				* ASN_FLAG_ALLOW_ZERO_PRIMITIVE (MMS service-body context only).
				* [IEDFuRL Bugs 4-7, 9 - Kanmani 2025 \S6.3.4-6.3.9]
				*/
				else if (length == 0U && !(flags & ASN_FLAG_ALLOW_ZERO_PRIMITIVE))
				{
					return_asn(ASN_REJECT_BADINT, offset);
				}

				break;
			}
		}

		offset += length;

		/*@ assert offset > offset_top; */
		/*@ assert end - offset < end - offset_top; */
	}

	return_asn(ASN_OK, 0U);
}

/* asn_filter_top -- shared pre-checks + recursive walk.
 * Called by safe_asn_filter (max_depth = SAFE_ASN_MAX_DEPTH) and directly
 * from safe_mms_filter for service body content
 * (max_depth = SAFE_ASN_MMS_BODY_MAX_DEPTH). */
/*@
requires
	asn_data == \null ||
	\valid_read(asn_data + (0 .. length - 1));

requires
	max_depth <= SAFE_ASN_MMS_BODY_MAX_DEPTH;

assigns
	\nothing;

ensures  // oversize messages are rejected
	asn_data != \null &&
	length > SAFE_ASN_MAX_MESSAGE
		==> \result.error == ASN_REJECT_SIZE;

ensures  // first tag not in whitelist rejected when ALLOW_CONTEXT not set
	asn_data				!= \null			&&
	length					> 0U				&&
	length					<= SAFE_ASN_MAX_MESSAGE		&&
	asn_data[0]				< ASN_TAG_WHITELIST_SIZE	&&
	ASN_TAG_WHITELIST[asn_data[0]]		== 0				&&
	(flags & ASN_FLAG_ALLOW_CONTEXT)	== 0U
		==> \result.error != ASN_OK;
*/
static SAFE_PURE SafeAsnResult asn_filter_top (
	const	u8	*const	asn_data,
	const	u32		length,
	const	u32		max_depth,
	const	u32		flags
)
{
	if (! asn_data) {
		return_asn(ASN_REJECT_NULL, 0);
	}

	if (length == 0U) {
		return_asn(ASN_OK, 0);
	}

	if (length > SAFE_ASN_MAX_MESSAGE) {
		return_asn(ASN_REJECT_SIZE, 0);
	}

	const u8 tag = asn_data[0];

	if (
		(
			tag >= ASN_TAG_WHITELIST_SIZE ||
			! ASN_TAG_WHITELIST[tag]
		)
			&&
		! (
			(tag >= 0x80U)				&&
			(tag < ASN_TAG_WHITELIST_SIZE)		&&
			(flags & ASN_FLAG_ALLOW_CONTEXT)
		)
	)
	{
		return_asn(ASN_REJECT_TAG, 0);
	}

	u32 node_count = 0U;

	return asn_filter_recursive (
			asn_data,
			length,
			0U,		/* start offset		*/
			length,		/* end			*/
			0U,		/* recursion depth	*/
			max_depth,	/* depth limit		*/
			&node_count,
			flags		/* allow_zero_primitive	*/
	);
}

/* asn_filter_recursive_relaxed -- BER structural validator for non-IEC protocols.
 * Same traversal logic as asn_filter_recursive but without the IEC 61850
 * profile restrictions: unrestricted INTEGER width, unrestricted OCTET/BIT
 * STRING size, GeneralizedTime/GeneralString tags (0x18, 0x1B) accepted,
 *
 * PrintableString (0x13) and SET (0x31) accepted (relaxed-only tags).
 *
 * SET admits up to SAFE_MAX_SET_MEMBERS members (default 16): X.509 RDNs are
 * usually single-member, but multi-valued RDNs and multi-valued directory
 * attributes (LDAP SET OF) are legal and common. No flags parameter -- always
 * relaxed. No ALLOW_ZERO_PRIMITIVE: non-IEC protocols do not use implicit-NULL fields. */
/*@
requires // that buffer is readable
    \valid_read(buffer + (0 .. buffer_length - 1));

requires // that walk region is within the buffer
    offset <= end <= buffer_length;

requires // that buffer size is limited
    buffer_length <= 65535;

requires // that recursion depth is bounded
    depth <= max_depth;

requires // that max_depth is within the configured upper bound
    max_depth <= SAFE_ASN_MMS_BODY_MAX_DEPTH;

requires // that node_count pointer is writable
    \valid(node_count);

requires // that node_count starts within bounds
    *node_count <= SAFE_ASN_RELAXED_MAX_NODES;

decreases // the walk region on each call (Termination)
    end - offset;

assigns // node_count
    *node_count;

ensures // node_count remains bounded
    *node_count <= SAFE_ASN_RELAXED_MAX_NODES;

ensures // node_count never decreases
    *node_count >= \old(*node_count);
*/
static SafeAsnResult asn_filter_recursive_relaxed (
	const	u8	*const	buffer,
	const	u32		buffer_length,
		u32		offset,
	const	u32		end,
	const	u32		depth,
	const	u32		max_depth,
		u32	*const	node_count
)
{
	/*@ ghost u32 offset_entry	= offset; */
	/*@ ghost u32 nc_entry		= *node_count; */

	/*@
		loop invariant
				offset	<= end;

		loop invariant
				end	<= buffer_length;

		loop invariant
				offset >= offset_entry;

		loop invariant
				*node_count <= SAFE_ASN_RELAXED_MAX_NODES;

		loop invariant
				*node_count >= nc_entry;

		loop assigns
				offset,
				*node_count;

		loop variant
				end - offset;
	*/
	while (offset < end)
	{
		if (*node_count >= SAFE_ASN_RELAXED_MAX_NODES) {
			return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
		}

		++(*node_count);

		/*@ ghost u32 offset_top = offset; */

		/* Tag: two-guard approach for WP tractability.
		 * Guard 1: PRIVATE class (0xC0-0xFF) -- never used; reject immediately. */

		/*@ assert offset < end <= buffer_length; */

		const u8 tag = buffer[offset++];

		if (tag >= ASN_TAG_WHITELIST_SIZE) {
			return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
		}

		/*@ assert (u32)tag < ASN_TAG_WHITELIST_SIZE; */

		/*
		* Guard 2: UNIVERSAL class (0x00-0x3F) -- must be in strict or relaxed
		* whitelist. APPLICATION (0x40-0x7F) and CONTEXT (0x80-0xBF) always pass.
		*/
		if (
			tag < 0x40U				&&
			! ASN_TAG_WHITELIST		[tag]	&&
			! ASN_TAG_WHITELIST_RELAXED	[tag]
		) {
			return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
		}

		/*@ assert offset > offset_top; */

		/* Multi-byte tag: skip continuation bytes */
		if ((tag & BER_HIGH_TAG_MASK) == BER_HIGH_TAG_MASK)
		{
			u32 continuation_bytes = 0U;

			/*@
				loop invariant offset <= buffer_length;
				loop invariant offset > offset_top;
				loop invariant 0 <= continuation_bytes <= SAFE_MAX_CONTINUATION_BYTES;
				loop assigns offset, continuation_bytes;
				loop variant (int)(SAFE_MAX_CONTINUATION_BYTES - continuation_bytes);
			*/
			while (
				offset			< buffer_length &&
				continuation_bytes	< SAFE_MAX_CONTINUATION_BYTES
			)
			{
				const u8 byte = buffer[offset++];

				++continuation_bytes;

				if ((byte & BER_CONTINUATION_BIT) == 0U) {
					break;
				}
			}

			if (continuation_bytes >= SAFE_MAX_CONTINUATION_BYTES) {
				return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
			}

			if (offset > end) {
				return_asn(ASN_REJECT_TRUNCATE, PREVIOUS(offset));
			}
		}

		/*@ assert offset > offset_top; */
		/*@ assert offset <= end; */

		/* Length */
		if (offset >= buffer_length) {
			return_asn(ASN_REJECT_TRUNCATE, offset);
		}

		/*@ assert offset < buffer_length; */

		const u8 length_byte = buffer[offset++];

		if (length_byte == BER_INDEFINITE_LENGTH) {
			return_asn(ASN_REJECT_INDEF, PREVIOUS(offset));
		}

		u32 length = 0U;

		if ((length_byte & BER_LONG_FORM_BIT) == 0U) {
			length = (u32)length_byte;
		}
		else
		{
			const u32 num_length_bytes = (u32) (
				length_byte & BER_LENGTH_MASK
			);

			if (num_length_bytes > ASN_MAX_LENGTH_BYTES) {
				return_asn(ASN_REJECT_LENGTH, offset);
			}

			const U32 Bytes_Required = ADD(offset, num_length_bytes);

			if (Bytes_Required.overflowed || Bytes_Required.value > buffer_length) {
				return_asn(ASN_REJECT_TRUNCATE, offset);
			}

			/*@
				loop invariant 0 <= i <= num_length_bytes;
				loop invariant offset <= buffer_length;
				loop invariant offset > offset_top;
				loop assigns i, length, offset;
				loop variant num_length_bytes - i;
			*/
			for (
				u32 i = 0U;
				(i < num_length_bytes) && (offset < buffer_length);
				++i
			)
			{
				if (length > (UINT32_MAX >> 8U)) {
					return_asn(ASN_REJECT_LENGTH, offset);
				}

				length = (length << 8U) | (u32)buffer[offset++];
			}
		}

		if (offset > end) {
			return_asn(ASN_REJECT_TRUNCATE, PREVIOUS(offset));
		}

		/*@ assert offset > offset_top; */
		/*@ assert offset <= end; */

		if (length > SAFE_ASN_MAX_MESSAGE) {
			return_asn(ASN_REJECT_SIZE, offset);
		}

		const U32 Remaining = SUBTRACT(end, offset);

		if (
			Remaining.underflowed	||
			length > end		||
			length > Remaining.value
		) {
			return_asn(ASN_REJECT_TRUNCATE, offset);
		}

		/*@ assert is_sanitized_length(length, offset, end); */
		/*@ assert offset + length <= end;           */
		/*@ assert offset + length <= buffer_length; */

		/*@ assert (u32)tag < ASN_TAG_WHITELIST_SIZE; */
		/*@ assert tag >= 0x40U || ASN_TAG_WHITELIST[tag] != 0U ||
			ASN_TAG_WHITELIST_RELAXED[tag] != 0U; */

		switch (tag)
		{
			case ASN_TAG_BOOLEAN:
			{
				if (length != 1U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (
					buffer[offset] != 0x00U &&
					buffer[offset] != 0x01U &&
					buffer[offset] != 0xFFU
				) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_NULL:
			{
				if (length != 0U) { /* NULL must be 0 bytes */
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_INTEGER:	/* INTEGER: machine-word width + minimal encoding */
			case ASN_TAG_ENUMERATED:/* same encoding rules as INTEGER */
			{
				/* No size restriction: X.509/Kerberos use large integers. */
				/* Minimal encoding check (DER S11.5) still applies. */

				if (length == 0U) {
					return_asn(ASN_REJECT_BADINT, offset);
				}

				if (length > 1U)
				{
					const U32 Next = ADD(offset, 1U);

					if (Next.overflowed) {
						return_asn(ASN_REJECT_TRUNCATE, offset);
					}

					const u8 b_and_sign = buffer[Next.value] & BER_SIGN_BIT;

					if (buffer[offset] == 0x00U && b_and_sign == 0U) {
						return_asn(ASN_REJECT_BADINT, offset);
					}

					if (buffer[offset] == 0xFFU && b_and_sign != 0U) {
						return_asn(ASN_REJECT_BADINT, offset);
					}
				}

				break;
			}

			case ASN_TAG_OCTET_STRING:
			{
				/* No size restriction: X.509 signatures can be large. */
				break;
			}

			case ASN_TAG_BITSTRING:
			{
				/* No size restriction; unused-bits byte still validated. */
				if (length > 0U)
				{
					/*@ assert offset < buffer_length; */
					if (buffer[offset] > 7U) {
						return_asn(ASN_REJECT_CONTENT, offset);
					}

					if (length == 1U && buffer[offset] != 0U) {
						return_asn(ASN_REJECT_CONTENT, offset);
					}
				}

				break;
			}

			case ASN_TAG_OID:
			{
				if (length == 0U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_IA5_STRING:
			{
				if (! is_valid_IA5string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_PRINTABLE_STRING:
			{
				if (! is_valid_printable_string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

#ifdef SAFE_ENABLE_ASN_VISIBLE_STRING
			case ASN_TAG_VISIBLE_STRING:
			{
				if (! is_valid_visible_string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}
#endif

			case 0x18U: /* GeneralizedTime:	treat as opaque leaf */
			case 0x1BU: /* GeneralString:	treat as opaque leaf */
			{
				break;
			}

			case ASN_TAG_SET:
			{
				if (depth >= max_depth) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				if (*node_count >= SAFE_ASN_RELAXED_MAX_NODES) {
					return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
				}

				const U32 Child_End = ADD(offset, length);

				if (Child_End.overflowed) {
					return_asn(ASN_REJECT_TRUNCATE, offset);
				}

				/* Count SET members; reject if empty or > SAFE_MAX_SET_MEMBERS. */
				{
					u32 mem_off		= offset;
					u32 member_count	= 0U;

					/*@
						loop invariant
							mem_off >= offset;

						loop invariant
							mem_off <= Child_End.value;

						loop invariant
							member_count <= SAFE_MAX_SET_MEMBERS;

						loop assigns
							mem_off,
							member_count;

						loop variant
							(int)(Child_End.value - mem_off);
					*/
					while (mem_off < Child_End.value)
					{
						if (member_count >= SAFE_MAX_SET_MEMBERS) {
							return_asn(ASN_REJECT_SET_MULTI, offset);
						}

						if (mem_off >= buffer_length) {
							return_asn(ASN_REJECT_TRUNCATE, offset);
						}

						/*@ ghost u32 mem_off_top = mem_off; */
						mem_off++;	/* consume tag byte */

						const U32 mem_len_R = read_length(buffer, buffer_length, &mem_off);
						if (mem_len_R.overflowed) {
							return_asn(ASN_REJECT_TRUNCATE, offset);
						}
						const u32 mem_len = mem_len_R.value;

						/*@ assert mem_off > mem_off_top; */

						const U32 Mem_End = ADD(mem_off, mem_len);

						if (Mem_End.overflowed || Mem_End.value > Child_End.value) {
							return_asn(ASN_REJECT_TRUNCATE, offset);
						}

						mem_off = Mem_End.value;
						member_count++;
					}

					if (member_count == 0U) {
						return_asn(ASN_REJECT_CONTENT, offset);
					}
				}

				const U32 Next_Depth = ADD(1U, depth);

				if (Next_Depth.overflowed) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				const SafeAsnResult result = asn_filter_recursive_relaxed (
								buffer,
								buffer_length,
								offset,
								Child_End.value,
								Next_Depth.value,
								max_depth,
								node_count
				);

				if (result.error != ASN_OK) {
					return result;
				}

				/*@ assert *node_count <= SAFE_ASN_RELAXED_MAX_NODES; */
				break;
			}

			case ASN_TAG_SEQUENCE:
			{
				if (depth >= max_depth) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				if (*node_count >= SAFE_ASN_RELAXED_MAX_NODES) {
					return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
				}

				const U32 Child_End = ADD(offset, length);

				if (Child_End.overflowed) {
					return_asn(ASN_REJECT_TRUNCATE, offset);
				}

				const U32 Next_Depth = ADD(1U, depth);

				if (Next_Depth.overflowed) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				const SafeAsnResult result = asn_filter_recursive_relaxed (
								buffer,
								buffer_length,
								offset,
								Child_End.value,
								Next_Depth.value,
								max_depth,
								node_count
				);

				if (result.error != ASN_OK) {
					return result;
				}

				/*@ assert *node_count <= SAFE_ASN_RELAXED_MAX_NODES; */
				break;
			}

			default: /* constructed context-specific / application tags */
			{
				if ((tag & 0x20U) != 0U)
				{
					if (depth >= max_depth) {
						return_asn(ASN_REJECT_DEPTH, offset);
					}

					if (*node_count >= SAFE_ASN_RELAXED_MAX_NODES) {
						return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
					}

					const U32 Child_End = ADD(offset, length);

					if (Child_End.overflowed) {
						return_asn(ASN_REJECT_TRUNCATE, offset);
					}

					const U32 Next_Depth = ADD(1U, depth);

					if (Next_Depth.overflowed) {
						return_asn(ASN_REJECT_DEPTH, offset);
					}

					const SafeAsnResult result = asn_filter_recursive_relaxed (
									buffer,
									buffer_length,
									offset,
									Child_End.value,
									Next_Depth.value,
									max_depth,
									node_count
					);

					if (result.error != ASN_OK) {
						return result;
					}

					/*@ assert *node_count <= SAFE_ASN_RELAXED_MAX_NODES; */
				}

				/*
				* Zero-length primitive implicit fields are valid in
				* LDAP/Kerberos (e.g. empty password [2] IMPLICIT OCTET
				* STRING length=0); accept silently in relaxed mode.
				*/
			}
		}

		/*@ assert *node_count <= SAFE_ASN_RELAXED_MAX_NODES; */

		offset += length;
	}

	return_asn(ASN_OK, 0U);
}

/*@
requires // buffer is null or readable
	asn_data == \null || \valid_read(asn_data + (0 .. length - 1));

assigns
	\nothing;

ensures // an accepted message is at least a tag byte plus one further byte
	\result.error == ASN_OK ==> length >= 2;
*/
SAFE_PURE SafeAsnResult safe_asn_filter (
	const	u8		*const	asn_data,
	const	u32		length
)
{
	/* A well-formed TLV needs at least a tag byte and a length byte.
	 * Reject empty or single-byte input rather than treating it as a
	 * vacuous accept, so an ASN_OK result always means a tag was read. */
	if (length < 2U) {
		return_asn(ASN_REJECT_TRUNCATE, 0U);
	}

	return asn_filter_top (
			asn_data,
			length,
			SAFE_ASN_MAX_DEPTH,
			0U
	);
}

/*@

requires // that the message size is limited
	length <= 65535;

requires // that the asn_data is null or readable
	asn_data == \null || \valid_read(asn_data + (0 .. length - 1));

assigns
	\nothing;	// Pure function: no memory is modified

ensures // that oversize messages are rejected

	asn_data != \null &&
	length > SAFE_ASN_MAX_MESSAGE
		==> \result.error == ASN_REJECT_SIZE;

ensures // that PRIVATE class tags (0xC0-0xFF) are always rejected

	asn_data			!= \null			&&
	length				> 0				&&
	length				<= SAFE_ASN_MAX_MESSAGE		&&
	(u8)asn_data[0]			>= ASN_TAG_WHITELIST_SIZE

		==> \result.error != ASN_OK;

ensures // that unknown UNIVERSAL tags (0x00-0x3F, not in either whitelist) are rejected

	asn_data			!= \null			&&
	length				> 0				&&
	length				<= SAFE_ASN_MAX_MESSAGE		&&
	(u8)asn_data[0]			< 0x40U				&&
	ASN_TAG_WHITELIST[(u8)asn_data[0]]	== 0			&&
	ASN_TAG_WHITELIST_RELAXED[(u8)asn_data[0]]	== 0

		==> \result.error != ASN_OK;
*/
SAFE_PURE SafeAsnResult safe_asn_filter_relaxed (
	const	u8	*const	asn_data,
	const	u32		length
)
{
	if (! asn_data) {
		return_asn(ASN_REJECT_NULL,  0);
	}

	if (length == 0U) {
		return_asn(ASN_OK, 0U);
	}

	if (length > SAFE_ASN_MAX_MESSAGE) {
		return_asn(ASN_REJECT_SIZE, 0U);
	}

	const u8 tag = asn_data[0];

	/* Two-guard approach matching asn_filter_recursive_relaxed. */
	if (tag >= ASN_TAG_WHITELIST_SIZE) {
		return_asn(ASN_REJECT_TAG, 0U);
	}

	if (
		tag < 0x40U				&&
		! ASN_TAG_WHITELIST		[tag]	&&
		! ASN_TAG_WHITELIST_RELAXED	[tag]
	) {
		return_asn(ASN_REJECT_TAG, 0U);
	}

	u32 node_count = 0U;

	return asn_filter_recursive_relaxed (
		asn_data,
		length,
		0U,
		length,
		0U,
		SAFE_ASN_RELAXED_MAX_DEPTH,
		&node_count
	);
}


/* ===============================================================
 * SafeASN.1 Parser - same validation + zero-copy node extraction
 *
 * Mirrors asn_filter_recursive but also records each TLV node
 * (tag, length, content pointer, depth) into the output array.
 * No heap allocation; nodes point into the caller's buffer.
 * =============================================================== */

/*@
requires // that the buffer is readable
	\valid_read(buffer + (0 .. buffer_length - 1));

requires // that the walk region is within the buffer
	offset <= end <= buffer_length;

requires // that buffer length is limited
	buffer_length <= 65535;

requires // that the recursion depth is bounded
	depth <= SAFE_ASN_MAX_DEPTH;

requires // that the node array is writable
	\valid(nodes + (0 .. SAFE_ASN_MAX_NODES - 1));

requires // the node count pointer is valid
	\valid(node_count);

requires // that the node count pointer is separated from buffer and nodes
	\separated(node_count, buffer + (0 .. buffer_length - 1));
requires
	\separated(nodes + (0 .. SAFE_ASN_MAX_NODES - 1),
		buffer + (0 .. buffer_length - 1));
requires
	\separated(nodes + (0 .. SAFE_ASN_MAX_NODES - 1), node_count);

requires // that the node count starts within bounds
	*node_count <= SAFE_ASN_MAX_NODES;

decreases // the walk region on each call (Termination)
	end - offset;

assigns
	*node_count,
	nodes[0 .. SAFE_ASN_MAX_NODES - 1];

ensures // nodes are only ever appended: count is monotonically non-decreasing
	*node_count >= \old(*node_count);

ensures // each TLV visited appends at most one node: increment is bounded
	*node_count <= \old(*node_count) + (end - offset);

ensures // node count never exceeds the array size
	*node_count <= SAFE_ASN_MAX_NODES;

*/
static SafeAsnResult asn_parse_recursive (
	const		u8		*const	buffer,
	const		u32			buffer_length,
			u32			offset,
	const		u32			end,
	const		u32			depth,
			SafeAsnNode	*const	nodes,
			u32		*const	node_count,
	const		u32			flags
)
{
	/*@ ghost u32 offset_entry	= offset; */
	/*@ ghost u32 nc_entry		= *node_count; */

	/*@
		loop invariant
				offset	<= end;

		loop invariant
				end	<= buffer_length;

		loop invariant
				offset >= offset_entry;

		loop invariant
				*node_count <= SAFE_ASN_MAX_NODES;

		loop invariant
				*node_count >= nc_entry;

		loop invariant	// nodes added bounded by bytes consumed (key for ensures_2)
				(integer)(*node_count) - (integer)nc_entry
				<= (integer)offset - (integer)offset_entry;

		loop assigns
				offset,
				*node_count,
				nodes[0 .. SAFE_ASN_MAX_NODES - 1];

		loop variant
				end - offset;
	*/
	while (offset < end)
	{
		if (*node_count >= SAFE_ASN_MAX_NODES) {
			return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
		}

		++(*node_count);

		const u32 node_idx = *node_count - 1U;	/* index of this node (parser only) */

		/*@ ghost u32 offset_top = offset; */

		/* Tag: whitelist check (context tags 0x80-0xBF gated by ASN_FLAG_ALLOW_CONTEXT) */

		/*@ assert offset < end <= buffer_length; */

		const u8 tag = buffer[offset++];

		if (
			(
				tag >= ASN_TAG_WHITELIST_SIZE		||
				! ASN_TAG_WHITELIST[tag]
			)
			&&
			! (
				(flags & ASN_FLAG_ALLOW_CONTEXT)	&&
				tag >= 0x80U				&&
				tag < ASN_TAG_WHITELIST_SIZE
			)
		)
		{
			return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
		}

		/*@ assert tag < 192;						*/
		/*@ assert is_sanitized_tag(tag) ||
		    ((flags & ASN_FLAG_ALLOW_CONTEXT) != 0U && tag >= 0x80U);	*/

		/* Multi-byte tag (context high-tag):
					skip up to 3 continuation bytes	*/

		/*@ assert offset > offset_top;				*/

		if ((tag & BER_HIGH_TAG_MASK) == BER_HIGH_TAG_MASK)
		{
			u32 continuation_bytes = 0U;

			/*@
				loop invariant
						offset <= buffer_length;

				loop invariant
						offset > offset_top;

				loop invariant
						0 <= continuation_bytes <= SAFE_MAX_CONTINUATION_BYTES;

				loop assigns
						offset,
						continuation_bytes;

				loop variant
						(int)(SAFE_MAX_CONTINUATION_BYTES - continuation_bytes);
			*/
			while (
				offset			< buffer_length &&
				continuation_bytes	< SAFE_MAX_CONTINUATION_BYTES
			)
			{
				const u8 byte = buffer[offset++];

				++continuation_bytes;

				if ((byte & BER_CONTINUATION_BIT) == 0U) {
					break;
				}
			}

			/* Unterminated high-tag: reject */
			if (continuation_bytes >= SAFE_MAX_CONTINUATION_BYTES) {
				return_asn(ASN_REJECT_TAG, PREVIOUS(offset));
			}

			/* Tag header must not extend past current TLV boundary */
			if (offset > end) {
				return_asn(ASN_REJECT_TRUNCATE, PREVIOUS(offset));
			}	
		}

		/*@ assert offset > offset_top; */
		/*@ assert offset <= end;	*/

		/* Length */
		if (offset >= buffer_length) {
			return_asn(ASN_REJECT_TRUNCATE, offset);
		}

		/*@ assert offset < buffer_length; */

		const u8 length_byte = buffer[offset++];

		if (length_byte == BER_INDEFINITE_LENGTH) {
			return_asn(ASN_REJECT_INDEF, PREVIOUS(offset));
		}

		u32 length = 0U;

		if ((length_byte & BER_LONG_FORM_BIT) == 0U) {
			length = (u32)length_byte;
		}
		else
		{
			const u32 num_length_bytes = (u32) (
						length_byte & BER_LENGTH_MASK
			);

			if (num_length_bytes > ASN_MAX_LENGTH_BYTES) {
				return_asn(ASN_REJECT_LENGTH, offset);
			}

			const U32 Bytes_Required = ADD(offset, num_length_bytes);

			if (Bytes_Required.overflowed || Bytes_Required.value > buffer_length) {
				return_asn(ASN_REJECT_TRUNCATE, offset);
			}

			/*@
				loop invariant
						0 <= i <= num_length_bytes;

				loop invariant
						offset <= buffer_length;
				loop invariant
						offset > offset_top;

				loop assigns
						i,
						length,
						offset;

				loop variant
						num_length_bytes - i;
			*/
			for
			(
				u32 i = 0U;
				(
					(i	< num_length_bytes	) &&
					(offset < buffer_length		)
				);
				++i
			)
			{
				if (length > (UINT32_MAX >> 8U)) { /* would overflow */
					return_asn(ASN_REJECT_LENGTH, offset);
				}

				length = (length << 8U) | (u32)buffer[offset++];
			}
		}

		/* Length header must not extend past current TLV boundary */
		if (offset > end) {
			return_asn(ASN_REJECT_TRUNCATE, PREVIOUS(offset));
		}

		/*@ assert offset > offset_top; */
		/*@ assert offset <= end; */

		if (length > SAFE_ASN_MAX_MESSAGE) {
			return_asn(ASN_REJECT_SIZE, offset);
		}

		const U32 Remaining = SUBTRACT(end, offset);

		if (
			Remaining.underflowed	||
			length > end		||
			length > Remaining.value
		) {
			return_asn(ASN_REJECT_TRUNCATE, offset);
		}

		/*@ assert offset + length <= end;		*/
		/*@ assert offset + length <= buffer_length;	*/

		/*@ assert tag < ASN_TAG_WHITELIST_SIZE;				*/
		/*@ assert is_sanitized_tag(tag) ||
		    ((flags & ASN_FLAG_ALLOW_CONTEXT) != 0U && tag >= 0x80U); */
		/*@ assert is_sanitized_length(length, offset, end);			*/

		switch (tag)
		{
			case ASN_TAG_BOOLEAN: /* BOOLEAN: 1 byte */
			{
				if (length != 1U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (
					buffer[offset] != 0x00U &&	/* false	*/
					buffer[offset] != 0x01U &&	/* BER true	*/
					buffer[offset] != 0xFFU		/* DER true	*/
				) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_NULL:
			{
				if (length != 0U) { /* NULL must be 0 bytes */
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_INTEGER:	/* INTEGER: machine-word width + minimal encoding */
			case ASN_TAG_ENUMERATED:/* same encoding rules as INTEGER */
			{
				/*
				* SafeASN.1 profile: restrict to machine-word widths.
				* IEC 61850 and MMS integer fields are always 1, 2, 4,
				* or 8 bytes; 3-byte and 5-7 byte encodings do not occur
				* in conformant messages and are a common fuzzer target.
				*/

				if (
					length != 1U &&
					length != 2U &&
					length != 4U &&
					length != 8U
				) {
					return_asn(ASN_REJECT_BADINT, offset);
				}

				/*
				* Non-minimal encoding check (BER S8.3.2 / DER S11.5):
				* leading 0x00 on a positive integer or 0xFF on a
				* negative integer means the value fits in fewer bytes.
				*/

				if (length != 1U)
				{
					const U32 Next = ADD(offset, 1U);

					if (Next.overflowed) {
						return_asn(ASN_REJECT_TRUNCATE, offset);
					}

					const u8 b_and_sign = buffer[Next.value] & BER_SIGN_BIT;

					if (buffer[offset] == 0x00U && b_and_sign == 0U) {
						return_asn(ASN_REJECT_BADINT, offset);
					}

					if (buffer[offset] == 0xFFU && b_and_sign != 0U) {
						return_asn(ASN_REJECT_BADINT, offset);
					}
				}

				break;
			}

			case ASN_TAG_UTF8_STRING: /* UTF8String (MMS mMSString / Unicode): size bounded */
			{
				if (length > SAFE_ASN_MAX_UTF8_STRING) {
					return_asn(ASN_REJECT_SIZE, offset);
				}

				break;
			}

			case ASN_TAG_OCTET_STRING: /* OCTET STRING: size bounded */
			{
				if (length > SAFE_ASN_MAX_OCTET_STRING) {
					return_asn(ASN_REJECT_SIZE, offset);
				}

				break;
			}

			case ASN_TAG_BITSTRING: /* BIT STRING: unused bits 0-7, size bounded */
			{
				if (length > SAFE_ASN_MAX_BIT_STRING) {
					return_asn(ASN_REJECT_SIZE, offset);
				}

				if (length > 0 && buffer[offset] > 7U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (length == 1U && buffer[offset] != 0U) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

			case ASN_TAG_OID:
			{
				if (length == 0U) { /* OID: must not be empty */
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				if (length > SAFE_ASN_MAX_OID) { /* OID: size bounded */
					return_asn(ASN_REJECT_SIZE, offset);
				}

				break;
			}

			case ASN_TAG_IA5_STRING:
			{
				/*@ assert length == 0 || \valid_read(buffer + offset + (0 .. length - 1)); */

				if (! is_valid_IA5string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}

#ifdef SAFE_ENABLE_ASN_VISIBLE_STRING
			case ASN_TAG_VISIBLE_STRING:
			{
				/*@ assert
					length == 0 ||
					\valid_read(buffer + offset + (0 .. length - 1));
				*/

				if (! is_valid_visible_string(buffer + offset, length)) {
					return_asn(ASN_REJECT_CONTENT, offset);
				}

				break;
			}
#endif

			/* Taint: all content checks passed for this TLV */

			/*@
				assert tag == ASN_TAG_BOOLEAN
					==> is_sanitized_boolean(buffer, offset);
			*/

			/*@
				assert tag == ASN_TAG_INTEGER
					==> is_sanitized_integer(buffer, offset, length);
			*/

			/*@
				assert tag == ASN_TAG_OCTET_STRING
					==> is_sanitized_octetstring(length);
			*/

			/*@
				assert tag == ASN_TAG_BITSTRING
					==> is_sanitized_bitstring(buffer, offset, length);
			*/

			/*@
				assert tag == ASN_TAG_OID
					==> is_sanitized_oid(length);
			*/

			/*@
				assert tag == ASN_TAG_VISIBLE_STRING
					==> is_sanitized_visible_string(length);
			*/

			case ASN_TAG_SEQUENCE: /* SEQUENCE: recurse into children */
			{
				if (depth >= SAFE_ASN_MAX_DEPTH) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				if (*node_count >= SAFE_ASN_MAX_NODES) {
					return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
				}

				const U32 Child_End = ADD(offset, length);

				if (Child_End.overflowed) {
					return_asn(ASN_REJECT_TRUNCATE, offset);
				}

				const U32 Next_Depth = ADD(1U, depth);

				if (Next_Depth.overflowed) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				/*@ assert Child_End.value <= buffer_length; */
				const SafeAsnResult child_result = asn_parse_recursive (
									buffer,
									buffer_length,
									offset,
									Child_End.value,
									Next_Depth.value,
									nodes,
									node_count,
									flags
				);

				if (child_result.error != ASN_OK) {
					return child_result;
				}

				break;
			}

		default: /* constructed context-specific / application tags: recurse */
		{
			if ((tag & 0x20U) != 0U)	/* constructed bit set */
			{
				if (depth >= SAFE_ASN_MAX_DEPTH) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				if (*node_count >= SAFE_ASN_MAX_NODES) {
					return_asn(ASN_REJECT_TOO_MANY_NODES, offset);
				}

				const U32 Child_End = ADD(offset, length);

				if (Child_End.overflowed) {
					return_asn(ASN_REJECT_TRUNCATE, offset);
				}

				const U32 Next_Depth = ADD(1U, depth);

				if (Next_Depth.overflowed) {
					return_asn(ASN_REJECT_DEPTH, offset);
				}

				/*@ assert Child_End.value <= buffer_length; */
				const SafeAsnResult child_result = asn_parse_recursive (
									buffer,
									buffer_length,
									offset,
									Child_End.value,
									Next_Depth.value,
									nodes,
									node_count,
									flags
				);

				if (child_result.error != ASN_OK) {
					return child_result;
				}
			}
			/* Primitive context-specific / application tag.
			 * These encode IMPLICIT-typed fields (INTEGER, BOOLEAN,
			 * ENUMERATED, ---); a zero-length encoding is a BER grammar
			 * violation for all such types.
			 * [IEDFuRL Bugs 4-7, 9 - Kanmani 2025 \S6.3.4-6.3.9] */
			else if (length == 0U)
			{
				return_asn(ASN_REJECT_BADINT, offset);
			}
		}
		}

		/* Record this node (parser only - filter has no nodes array) */
		nodes[node_idx].tag	= tag;
		nodes[node_idx].length	= length;
		nodes[node_idx].content	= &buffer[offset];
		nodes[node_idx].depth	= depth;

		offset += length;

		/*@ assert offset > offset_top;			*/
		/*@ assert end - offset < end - offset_top;	*/
	}

	return_asn(ASN_OK, 0U);
}

/*@

requires // a limit on message size
	length <= 65535;

requires // that asn_data is empty or readable
	length == 0 ||
	\valid_read(asn_data + (0 .. length - 1));

requires // that out is a valid writable struct
	\valid(out);

requires // that out->nodes does not alias asn_data
	length == 0 ||
	\separated(out->nodes + (0 .. SAFE_ASN_MAX_NODES - 1),
	           asn_data + (0 .. length - 1));

requires // that &out->node_count does not alias asn_data
	length == 0 ||
	\separated(&out->node_count, asn_data + (0 .. length - 1));

assigns	out->error,
	out->reject_at,
	out->node_count,
	out->nodes[0 .. SAFE_ASN_MAX_NODES - 1];

ensures // that oversize messages are always rejected
	length > SAFE_ASN_MAX_MESSAGE
		==> out->error == ASN_REJECT_SIZE;

ensures // that if first tag not in whitelist, then it is always rejected
	length				> 0				&&
	length				<= SAFE_ASN_MAX_MESSAGE		&&
	asn_data[0]			< ASN_TAG_WHITELIST_SIZE	&&
	ASN_TAG_WHITELIST[asn_data[0]]	== 0
		==> out->error != ASN_OK;

ensures // that node count is bounded
	out->node_count <= SAFE_ASN_MAX_NODES;
*/
u32 safe_asn_parse (
	const	u8		*const	asn_data,
		u32		length,
	SafeAsnParseResult	*const	out
)
{
	if (! out) {
		return (ASN_REJECT_NULL);
	}

	out->error	= ASN_OK;
	out->reject_at	= 0U;
	out->node_count	= 0U;

	if (! asn_data) {
		return (out->error = ASN_REJECT_NULL);
	}

	if (length == 0U) {
		return ASN_OK;
	}

	if (length > SAFE_ASN_MAX_MESSAGE) {
		return (out->error = ASN_REJECT_SIZE);
	}

	/* Pre-check: first tag must be accepted */

	const u8 tag = asn_data[0];

	if (tag >= ASN_TAG_WHITELIST_SIZE || ! ASN_TAG_WHITELIST[tag]) {
		return (out->error = ASN_REJECT_TAG);
	}

	const SafeAsnResult result = asn_parse_recursive (
					asn_data,
					length,
					0U,
					length,
					0U,
					out->nodes,
					&out->node_count,
					0U
	);

	out->error	= result.error;
	out->reject_at	= result.reject_at;

	return out->error;
}


/* ==========================================================
 * SafeMMS - PDU tag + service whitelists
 * ========================================================== */

static const u8 MMS_PDU_WHITELIST[176] = {
	[MMS_PDU_CONFIRMED_REQUEST	] = 1, /* confirmed-Request	*/
	[MMS_PDU_CONFIRMED_RESPONSE	] = 1, /* confirmed-Response	*/
	[MMS_PDU_CONFIRMED_ERROR	] = 1, /* confirmed-ErrorPDU	*/
	[MMS_PDU_UNCONFIRMED		] = 1, /* unconfirmed		*/
	[MMS_PDU_REJECT			] = 1, /* rejectPDU		*/
#ifdef SAFE_ENABLE_MMS_CANCEL
	[MMS_PDU_CANCEL_REQUEST		] = 1, /* cancelRequestPDU	*/
	[MMS_PDU_CANCEL_RESPONSE	] = 1, /* cancelResponsePDU	*/
	[MMS_PDU_CANCEL_ERROR		] = 1, /* cancelErrorPDU	*/
#endif
	[MMS_PDU_INITIATE_REQUEST	] = 1, /* initiate-Request	*/
	[MMS_PDU_INITIATE_RESPONSE	] = 1, /* initiate-Response	*/
	[MMS_PDU_INITIATE_ERROR		] = 1, /* initiate-Error	*/
	[MMS_PDU_CONCLUDE_REQUEST	] = 1, /* conclude-Request	*/
	[MMS_PDU_CONCLUDE_RESPONSE	] = 1, /* conclude-Response	*/
	[MMS_PDU_CONCLUDE_ERROR		] = 1, /* conclude-Error	*/
};

static const u8 MMS_SERVICE_WHITELIST[80] = {

#ifdef SAFE_ENABLE_MMS_STATUS
	/* status [0] disabled by default (not needed for IEC 61850). */

	[0] = 1, /* status		*/
#endif

	[1] = 1, /* getNameList	*/

#ifdef SAFE_ENABLE_MMS_IDENTIFY
	/* identify [2] disabled by default (info disclosure). */

	[2] = 1, /* identify		*/
#endif

	[4] = 1, /* read		*/
	[5] = 1, /* write		*/
	[6] = 1, /* getVarAccessAttr	*/

	[11] = 1, /* defineNVL		*/  /* required: IEDs use this to set up data sets */
	[12] = 1, /* getNVLAttributes	*/
#ifdef SAFE_ENABLE_MMS_DELETE_NVL
	/* deleteNVL [13] disabled by default (destroys configured data sets). */
	[13] = 1, /* deleteNVL		*/
#endif

	[46] = 1, /* obtainFile		*/

	[72] = 1, /* fileOpen		*/
	[73] = 1, /* fileRead		*/
	[74] = 1, /* fileClose		*/
	[77] = 1, /* fileDirectory	*/
	/* [75] fileRename and [76] fileDelete unconditionally removed from SafeMMS */
};

/*@

requires // that length is always less than Maximum PDU size
	length <= 65535;

requires // that the mms_pdu to be empty or readable
	length == 0 ||
	\valid_read(mms_pdu + (0 .. length - 1));

assigns
	\nothing;	// Pure function: no memory is modified


ensures	// that oversize PDU is always rejected
	length > 65535
		==> \result.error == MMS_REJECT_SIZE;

ensures	// that empty input is always rejected
	length == 0
		==> \result.error == MMS_REJECT_TRUNCATE;


ensures	// that PDU tag not in whitelist is rejected
	length				> 0				&&
	length				<= 65535			&&
	mms_pdu[0]			< sizeof(MMS_PDU_WHITELIST)	&&
	MMS_PDU_WHITELIST[mms_pdu[0]]	== 0
		==> \result.error == MMS_REJECT_PDU_TAG;
*/
SAFE_PURE SafeMmsResult safe_mms_filter (
	const	u8	*const	mms_pdu,
	const	u32	length
)
{
	SafeMmsResult out = {
			.error		= MMS_OK,
			.reject_at	= 0U,
			.service_tag	= 0U
	};

	if (length == 0U) {
		return_filter (MMS_REJECT_TRUNCATE,0U);
	}

	if (length > SAFE_MMS_MAX_PDU) {
		return_filter (MMS_REJECT_SIZE,0U);
	}

	const u8 pdu_tag = mms_pdu[0];

	/* PDU tag whitelist */
	if (pdu_tag >= sizeof(MMS_PDU_WHITELIST) || ! MMS_PDU_WHITELIST[pdu_tag]) {
		return_filter (MMS_REJECT_PDU_TAG,0U);
	}

	/*@
		assert
			mms_pdu[0] < sizeof(MMS_PDU_WHITELIST) &&
			MMS_PDU_WHITELIST[mms_pdu[0]] != 0;
	*/

	u32 offset = 1U;

	/*@
		assert
			offset <= length;
	*/

	/*@
		assert
			\separated(&offset, mms_pdu + (0 .. length - 1));
	*/

	const U32 pdu_len_R = read_length(mms_pdu, length, &offset);
	if (pdu_len_R.overflowed) {
		return_filter (MMS_REJECT_TRUNCATE,offset);
	}
	const u32 pdu_len = pdu_len_R.value;

	/*@ assert offset <= length; */

	const U32 PDU_End = ADD(offset, pdu_len);

	if (PDU_End.overflowed || PDU_End.value > length) {
		return_filter (MMS_REJECT_TRUNCATE,offset);
	}

	/*@ assert offset + pdu_len <= length; */

	const u32 pdu_end = PDU_End.value;

	/*@ assert pdu_end <= length; */

	if (pdu_tag == MMS_PDU_CONFIRMED_REQUEST) /* Confirmed: invokeId -> service tag */
	{		/* [0] IMPLICIT SEQUENCE per ISO 9506-2: no inner 0x30 */

		/*@ assert offset < pdu_end ==> offset < length; */

		if (offset >= pdu_end || mms_pdu[offset] != ASN_TAG_INTEGER) {
			return_filter (MMS_REJECT_INVOKE_ID,offset);
		}

		++offset;

		/*@ assert offset <= length; */

		const U32 invoke_len_R = read_length(mms_pdu, length, &offset);
		if (invoke_len_R.overflowed) {
			return_filter (MMS_REJECT_INVOKE_ID,offset);
		}
		const u32 invoke_len = invoke_len_R.value;

		/*@ assert offset <= length; */

		/*
		*BER INTEGER requires at least 1 content byte; length=0 is a
		* grammar violation.  Upper bound 4 covers invokeID up to 2^31-1 (Unsigned32).
		* [IEDFuRL Bug 2 - Kanmani 2025 \S6.3.2]
		*/
		if (invoke_len == 0U || invoke_len > 4U) {
			return_filter (MMS_REJECT_INVOKE_ID,offset);
		}

		const U32 Invoke_Sum = ADD(offset, invoke_len);

		if (Invoke_Sum.overflowed || Invoke_Sum.value > length) {
			return_filter (MMS_REJECT_TRUNCATE,offset);
		}

		offset = Invoke_Sum.value;

		if (offset >= pdu_end) {
			return_filter (MMS_REJECT_TRUNCATE,offset);
		}

		/* Read context tag number (service) - may be multi-byte */

		/*@ assert pdu_end	<= length;	*/
		/*@ assert offset	< pdu_end;	*/
		/*@ assert offset	< length;	*/

		const	u8		service_byte	= mms_pdu[offset++];
			u32	service		= (u32) (
					service_byte & BER_HIGH_TAG_MASK
			);

		if (service == BER_HIGH_TAG_MASK)
		{
			/* High-tag-number: base-128 decode */

			u8 continuation_bytes = 0U;

			service = 0U;

			/*@
				loop invariant
						offset <= length;

				loop assigns
						offset,
						service,
						continuation_bytes;

				loop variant
						length - offset;
			*/
			while (offset < length && continuation_bytes < SAFE_MAX_CONTINUATION_BYTES)
			{
				const u8 byte = mms_pdu[offset++];

				++continuation_bytes;

				service = (service << 7U) | (u32) (
								byte & BER_LENGTH_MASK
				);

				if ((byte & BER_CONTINUATION_BIT) == 0U) {
					break;
				}
			}

			if (continuation_bytes >= SAFE_MAX_CONTINUATION_BYTES) {
				return_filter (MMS_REJECT_SERVICE,PREVIOUS(offset));
			}
		}

		out.service_tag = service;

		if (
			service >= sizeof(MMS_SERVICE_WHITELIST) ||
			! MMS_SERVICE_WHITELIST[service]
		) {
			return_filter (MMS_REJECT_SERVICE,PREVIOUS(offset));
		}

		/*@
			assert
				service < sizeof(MMS_SERVICE_WHITELIST) &&
				MMS_SERVICE_WHITELIST[service] != 0;
		*/

		/* Pass service body through SafeASN.1: catches oversized primitive
		 * types (e.g. BIT STRING > 128 B), bad tags, and length-field
		 * overruns inside the service content (CVE-2020-7054 class). */
		{
			u32 body_start = offset;	/* offset is past all service tag bytes */

			const U32 body_len_R = read_length(mms_pdu, length, &body_start);
			if (body_len_R.overflowed) {
				return_filter (MMS_REJECT_TRUNCATE,body_start);
			}
			const u32 body_len = body_len_R.value;

			const U32 Body_End = ADD(body_start, body_len);

			if (Body_End.overflowed || Body_End.value > pdu_end) {
				return_filter (MMS_REJECT_TRUNCATE,body_start);
			}

			if (body_len > 0U)
			{
				const SafeAsnResult asn_r = asn_filter_top (
								mms_pdu + body_start,
								body_len,
								SAFE_ASN_MMS_BODY_MAX_DEPTH,
								ASN_FLAG_ALLOW_ZERO_PRIMITIVE | ASN_FLAG_ALLOW_CONTEXT
				);

				if (asn_r.error != ASN_OK) {
					const U32 reject_at	= ADD(body_start, asn_r.reject_at);

					return_filter (MMS_REJECT_BODY,reject_at.overflowed ? body_start : reject_at.value);
				}
			}
		}
	}
	else if (pdu_tag == MMS_PDU_UNCONFIRMED)	/* Unconfirmed: informationReport only	*/
	{
		/*
		* ISO 9506-2: unconfirmed [3] IMPLICIT UnconfirmedPDU, where
		* UnconfirmedPDU ::= SEQUENCE { unconfirmedService UnconfirmedService }.
		* With the outer IMPLICIT tag the body appears as one of:
		*	(a) 0xa0 .. -- [0] informationReport directly (no SEQUENCE wrapper)
		*	Most real IEC 61850 stacks (e.g. libIEC61850, SEL, GE).
		*
		*	(b) 0x30 seq-len 0xa0 .. - SEQUENCE-wrapped encoding
		*       Used by some stacks / test tools.
		*
		* Both are accepted; any other inner tag is rejected.
		*/
		if (offset >= pdu_end) {
			return_filter (MMS_REJECT_INNER_SEQ,offset);
		}

		if (mms_pdu[offset] == ASN_TAG_SEQUENCE)	/* SEQUENCE-wrapped encoding */
		{
			++offset;

			/*@ assert offset <= length; */

			const U32 seq_len_R = read_length(mms_pdu, length, &offset);

			if (seq_len_R.overflowed) {
				return_filter (MMS_REJECT_TRUNCATE,offset);
			}

			/*@ assert offset <= length; */

			if (offset >= pdu_end) {
				return_filter (MMS_REJECT_TRUNCATE,offset);
			}

			/*@ assert offset < length; */

			const u8 service_byte = mms_pdu[offset++];

			const u32 service = (u32)(service_byte & BER_HIGH_TAG_MASK);

			out.service_tag = service;

			if (service != MMS_SERVICE_INFORMATION_REPORT) {
				return_filter (MMS_REJECT_SERVICE,PREVIOUS(offset));
			}
		}
		else if (mms_pdu[offset] == MMS_PDU_CONFIRMED_REQUEST) /* direct [0] informationReport */
		{
			out.service_tag = MMS_SERVICE_INFORMATION_REPORT;

			++offset;

			/*@ assert offset <= length; */
		}
		else					/* unknown inner tag		*/ {
			return_filter (MMS_REJECT_INNER_SEQ,offset);
		}

		/* Validate the informationReport body through SafeASN.1, as in the
		 * confirmed-request/response paths. In both encodings offset points at
		 * the informationReport content's length octet. */
		{
			u32 body_start = offset;

			const U32 Body_Len = read_length(mms_pdu, length, &body_start);

			if (Body_Len.overflowed) {
				return_filter (MMS_REJECT_TRUNCATE,body_start);
			}

			const u32 body_len = Body_Len.value;

			const U32 Body_End = ADD(body_start, body_len);

			if (Body_End.overflowed || Body_End.value > pdu_end) {
				return_filter (MMS_REJECT_TRUNCATE,body_start);
			}

			if (body_len > 0U)
			{
				const SafeAsnResult asn_r = asn_filter_top (
								mms_pdu + body_start,
								body_len,
								SAFE_ASN_MMS_BODY_MAX_DEPTH,
								ASN_FLAG_ALLOW_ZERO_PRIMITIVE | ASN_FLAG_ALLOW_CONTEXT
				);

				if (asn_r.error != ASN_OK) {
					const U32 reject_at	= ADD(body_start, asn_r.reject_at);

					return_filter (MMS_REJECT_BODY,reject_at.overflowed ? body_start : reject_at.value);
				}
			}
		}
	}
	else if (pdu_tag == MMS_PDU_CONFIRMED_RESPONSE)	/* confirmed-response: invokeId -> service tag */
	{				/* mirrors confirmed-request structure	*/

		if (offset >= pdu_end || mms_pdu[offset] != ASN_TAG_INTEGER) {
			return_filter (MMS_REJECT_INVOKE_ID,offset);
		}

		++offset;

		/*@ assert offset <= length; */

		const U32 invoke_len_R = read_length(mms_pdu, length, &offset);
		if (invoke_len_R.overflowed) {
			return_filter (MMS_REJECT_INVOKE_ID,offset);
		}
		const u32 invoke_len = invoke_len_R.value;

		/* Same grammar constraint as confirmed-request invokeID.
		 * [IEDFuRL Bug 2 - Kanmani 2025 \S6.3.2] */
		if (invoke_len == 0U || invoke_len > 4U) {
			return_filter (MMS_REJECT_INVOKE_ID,offset);
		}

		const U32 resp_inv_sum = ADD(offset, invoke_len);

		if (resp_inv_sum.overflowed || resp_inv_sum.value > length) {
			return_filter (MMS_REJECT_TRUNCATE,offset);
		}

		offset = resp_inv_sum.value;

		if (offset >= pdu_end) {
			return_filter (MMS_REJECT_TRUNCATE,offset);
		}

		const	u8	resp_service_byte	= mms_pdu[offset++];

			u32	resp_service		= (u32) (
				resp_service_byte & BER_HIGH_TAG_MASK
			);

		if (resp_service == BER_HIGH_TAG_MASK)
		{
			u8 continuation_bytes	= 0U;

			resp_service		= 0U;

			/*@
				loop invariant
						offset <= length;

				loop assigns
						offset,
						resp_service,
						continuation_bytes;

				loop variant
						length - offset;
			*/
			while (
				offset			< length &&
				continuation_bytes	< SAFE_MAX_CONTINUATION_BYTES
			)
			{
				const u8 byte = mms_pdu[offset++];

				++continuation_bytes;

				resp_service = (resp_service << 7U) | (u32)(
							byte & BER_LENGTH_MASK
				);

				if ((byte & BER_CONTINUATION_BIT) == 0U) {
					break;
				}
			}

			if (continuation_bytes >= SAFE_MAX_CONTINUATION_BYTES) {
				return_filter (MMS_REJECT_SERVICE,PREVIOUS(offset));
			}
		}

		out.service_tag = resp_service;

		if (
			resp_service >= sizeof(MMS_SERVICE_WHITELIST) ||
			! MMS_SERVICE_WHITELIST[resp_service]
		) {
			return_filter (MMS_REJECT_SERVICE,PREVIOUS(offset));
		}

		/* Validate response body through SafeASN.1 (CVE-2024-45970/45971 class) */
		{
			u32 body_start = offset;

			const U32 body_len_R = read_length(mms_pdu, length, &body_start);
			if (body_len_R.overflowed) {
				return_filter (MMS_REJECT_TRUNCATE,body_start);
			}
			const u32 body_len = body_len_R.value;
			const U32 Body_End = ADD(body_start, body_len);

			if (Body_End.overflowed || Body_End.value > pdu_end) {
				return_filter (MMS_REJECT_TRUNCATE,body_start);
			}

			if (body_len > 0U)
			{
				const SafeAsnResult asn_r = asn_filter_top (
								mms_pdu + body_start,
								body_len,
								SAFE_ASN_MMS_BODY_MAX_DEPTH,
								ASN_FLAG_ALLOW_ZERO_PRIMITIVE | ASN_FLAG_ALLOW_CONTEXT
				);

				if (asn_r.error != ASN_OK) {
					const U32 Reject_At	= ADD(body_start, asn_r.reject_at);

					return_filter (MMS_REJECT_BODY,Reject_At.overflowed ? body_start : Reject_At.value);
				}
			}
		}
	}
	else if (pdu_tag == MMS_PDU_INITIATE_REQUEST || pdu_tag == MMS_PDU_INITIATE_RESPONSE)
	{			/* body must be non-empty and start	*/
				/* with a context-specific tag (0x80-BF)*/

		if (pdu_len < 2U) {
			return_filter (MMS_REJECT_TRUNCATE,offset);
		}

		if ((mms_pdu[offset] & 0x80U) == 0U)	/* first inner byte: not context tag */ {
			return_filter (MMS_REJECT_INNER_SEQ,offset);
		}

		/* Walk the full body through SafeASN.1: catches zero-length
		 * IMPLICIT INTEGER fields such as localDetailCalling,
		 * proposedVersionNumber, proposedMaxServOutstandingCalled, and
		 * proposedDataStructureNestingLevel set to length 0x00.
		 * [IEDFuRL Bugs 4-7 - Kanmani 2025 \S6.3.4-6.3.7] */
		{
			const SafeAsnResult init_r = asn_filter_top (
							mms_pdu + offset,
							pdu_len,
							SAFE_ASN_MMS_BODY_MAX_DEPTH,
							ASN_FLAG_ALLOW_CONTEXT	/* Initiate body uses IMPLICIT context
										 * fields [0]-[4]; allow the context class but
										 * NOT zero-length primitives (no ALLOW_ZERO_PRIMITIVE)
										 * so valid initiate PDUs pass while len=0 IMPLICIT
										 * INTEGER fields are rejected as ASN_REJECT_BADINT
										 * [IEDFuRL Bugs 4-7 - Kanmani 2025 \S6.3.4-6.3.7] */
			);

			if (init_r.error != ASN_OK) {
				const U32 Reject_At	= ADD(offset, init_r.reject_at);

				return_filter (MMS_REJECT_BODY,Reject_At.overflowed ? offset : Reject_At.value);
			}
		}
	}
	else if (pdu_tag == MMS_PDU_CONCLUDE_REQUEST ||
		 pdu_tag == MMS_PDU_CONCLUDE_RESPONSE)	/* conclude-request/response: no body */
	{
		if (pdu_len != 0U) {
			return_filter (MMS_REJECT_TRUNCATE,offset);
		}
	}
	else if (pdu_tag == MMS_PDU_CONFIRMED_ERROR ||
		 pdu_tag == MMS_PDU_REJECT		||
		 pdu_tag == MMS_PDU_CANCEL_REQUEST	||
		 pdu_tag == MMS_PDU_CANCEL_RESPONSE	||
		 pdu_tag == MMS_PDU_CANCEL_ERROR	||
		 pdu_tag == MMS_PDU_INITIATE_ERROR	||
		 pdu_tag == MMS_PDU_CONCLUDE_ERROR)	/* error/reject/cancel PDUs: validate body as ASN.1 */
	{
		if (pdu_len > 0U)
		{
			const SafeAsnResult asn_r = asn_filter_top (
							mms_pdu + offset,
							pdu_len,
							SAFE_ASN_MAX_DEPTH,	/* ISO 9506-2 ServiceError nests to depth 5+ */
							ASN_FLAG_ALLOW_ZERO_PRIMITIVE | ASN_FLAG_ALLOW_CONTEXT	/* IMPLICIT NULL fields in error bodies */
			);

			if (asn_r.error != ASN_OK) {
				const U32 Reject_At	= ADD(offset, asn_r.reject_at);

				return_filter (MMS_REJECT_BODY,Reject_At.overflowed ? offset : Reject_At.value);
			}
		}
	}

	return out;
}


/* ==========================================================
 * SafeDNP3 - FC/group/variation/qualifier whitelists
 * ========================================================== */

static const u8 DNP3_FUNCTION_CODE_WHITELIST[136] = {

	[0x00] = 1, /* confirm	*/
	[0x01] = 1, /* read	*/
	[0x02] = 1, /* write	*/
	[0x03] = 1, /* select	*/
	[0x04] = 1, /* operate	*/

#ifdef SAFE_ENABLE_DNP3_DIRECT_OPERATE
/* direct operate [0x05] disabled by default (no SBO confirmation).*/
	[0x05] = 1, /* direct-operate */
#endif

#ifdef SAFE_ENABLE_DNP3_DIRECT_OPERATE_NR
/* direct operate no-ack [0x06] disabled by default. */
	[0x06] = 1, /* direct-operate-nr */
#endif

#ifdef SAFE_ENABLE_DNP3_COUNTER_FREEZE
/* counter freeze [0x07-0x0C] disabled by default.	*/

	[0x07] = 1, /* immed-freeze			*/
	[0x08] = 1, /* immed-freeze-nr			*/
	[0x09] = 1, /* freeze-clear			*/
	[0x0A] = 1, /* freeze-clear-nr			*/
	[0x0B] = 1, /* freeze-at-time			*/
	[0x0C] = 1, /* freeze-at-time-nr		*/
#endif

#ifdef SAFE_ENABLE_DNP3_COLD_RESTART
/* cold restart [0x0D] disabled by default (DoS risk).	*/
	[0x0D] = 1, /* cold-restart			*/
#endif

#ifdef SAFE_ENABLE_DNP3_WARM_RESTART
/* warm restart [0x0E] disabled by default (DoS risk).	*/
	[0x0E] = 1, /* warm-restart			*/
#endif

	[0x14] = 1, /* enable-unsol			*/

#ifdef SAFE_ENABLE_DNP3_DISABLE_UNSOLICITED
/* disable-unsol [0x15] disabled by default (suppresses alarm reporting). */
	[0x15] = 1, /* disable-unsol			*/
#endif

#ifdef SAFE_ENABLE_DNP3_ASSIGN_CLASS
/* assign-class [0x16] disabled by default (commissioning-phase operation). */
	[0x16] = 1, /* assign-class			*/
#endif

	[0x17] = 1, /* delay-measure			*/

#ifdef SAFE_ENABLE_DNP3_FILE_TRANSFER
/* file transfer [0x19-0x1E] disabled by default.	*/

	[0x19] = 1, /* open-file			*/
	[0x1A] = 1, /* close-file			*/
	[0x1B] = 0, /* delete-file is ALWAYS disabled	*/
	[0x1C] = 1, /* get-file-info			*/
	[0x1D] = 1, /* authenticate			*/
	[0x1E] = 1, /* abort-file			*/
#endif

	[0x81] = 1, /* response				*/
	[0x82] = 1, /* unsol-response			*/
};

static const u8 DNP3_GROUP_WHITELIST[123] = {

	[ 1] = 1, /* binary input			*/
	[ 2] = 1, /* binary input event			*/
	[ 3] = 1, /* double-bit binary input		*/
	[ 4] = 1, /* double-bit binary input event	*/

	[10] = 1, /* binary output			*/
	[11] = 1, /* binary output event		*/

	[12] = 1, /* CROB				*/

	[20] = 1, /* binary counter			*/
	[21] = 1, /* frozen counter			*/
	[22] = 1, /* binary counter event		*/
	[23] = 1, /* frozen counter event		*/

	[30] = 1, /* analog input			*/
	[31] = 1, /* frozen analog input			*/

	[32] = 1, /* analog input event			*/
	[33] = 1, /* frozen analog input event		*/

	[40] = 1, /* analog output			*/
	[41] = 1, /* analog output block		*/
	[42] = 1, /* analog output event		*/

	[50] = 1, /* time and date			*/
	[51] = 1, /* time CTO			*/
	[52] = 1, /* time delay			*/

	[60] = 1, /* class objects		*/

	[80] = 1, /* internal ind		*/

#ifdef SAFE_ENABLE_DNP3_SECURE_AUTH

/* secure authentication [120-122] disabled by default. */

	[120] = 1, /* authentication		*/
	[121] = 1, /* security statistics	*/
	[122] = 1, /* security statistic events	*/
#endif

};

#define DNP3_VARIATION_INVALID	0x00U	/* not permitted; also the unlisted default	*/
#define DNP3_VARIATION_PACKED	0xFFU	/* packed bits: ceil(count/8)			*/
#define DNP3_VARIATION_ANY	0xFDU	/* variation 0 / class: no fixed size		*/

/* Short aliases used inside the DNP3_POINTS source list below */
#define PKD DNP3_VARIATION_PACKED
#define ANY DNP3_VARIATION_ANY

/*
 * Single source of truth for permitted DNP3 objects: each X(group, variation,
 * octet-size) is one accepted (group,variation), its fixed on-wire object size
 * verified against IEEE Std 1815-2012 Annex A.  DNP3_POINT_SIZE is generated
 * from this list so the table and the permitted set can never drift.  Any
 * (group,variation) NOT listed defaults to DNP3_VARIATION_INVALID (0) and is
 * rejected -- fail-closed.
 *
 * Size building blocks: flag/control octet (BSTR8) = 1, UINT16/INT16 = 2,
 * UINT32/INT32/FLT32 = 4, DNP3TIME (UINT48) = 6, FLT64 = 8.
 */
#define DNP3_POINTS(X)							\
	/* g1  Binary Input               (A.2)  */			\
	X( 1,0,ANY) X( 1,1,PKD) X( 1,2, 1)				\
	/* g2  Binary Input Event         (A.3)  */			\
	X( 2,0,ANY) X( 2,1, 1) X( 2,2, 7) X( 2,3, 3)			\
	/* g3  Double-bit Binary Input    (A.4)  */			\
	X( 3,0,ANY) X( 3,1,PKD) X( 3,2, 1)				\
	/* g4  Double-bit Binary In Evt   (A.5)  */			\
	X( 4,0,ANY) X( 4,1, 1) X( 4,2, 7) X( 4,3, 3)			\
	/* g10 Binary Output              (A.6)  */			\
	X(10,0,ANY) X(10,1,PKD) X(10,2, 1)				\
	/* g11 Binary Output Event        (A.7: only v1,v2 defined) */	\
	X(11,0,ANY) X(11,1, 1) X(11,2, 7)				\
	/* g12 CROB                       (A.8.1) */			\
	X(12,1,11)							\
	/* g20 Counter                    (A.10) */			\
	X(20,0,ANY) X(20,1, 5) X(20,2, 3) X(20,5, 4) X(20,6, 2)		\
	/* g21 Frozen Counter (A.11: v5/v6 are flag+time; the */	\
	/*     without-flag forms live at v9/v10, unreachable here) */	\
	X(21,0,ANY) X(21,1, 5) X(21,2, 3)				\
	/* g22 Counter Event              (A.12: v5/v6 with-time) */	\
	X(22,0,ANY) X(22,1, 5) X(22,2, 3) X(22,5,11) X(22,6, 9)		\
	/* g23 Frozen Counter Event       (A.13: v5/v6 with-time) */	\
	X(23,0,ANY) X(23,1, 5) X(23,2, 3) X(23,5,11) X(23,6, 9)		\
	/* g30 Analog Input               (A.14) */			\
	X(30,0,ANY) X(30,1, 5) X(30,2, 3) X(30,3, 4) X(30,4, 2) X(30,5, 5) \
	/* g31 Frozen Analog Input        (A.15) */			\
	X(31,0,ANY) X(31,1, 5) X(31,2, 3) X(31,3,11) X(31,4, 9)		\
	/* g32 Analog Input Event         (A.16) */			\
	X(32,0,ANY) X(32,1, 5) X(32,2, 3) X(32,3,11) X(32,4, 9) X(32,5, 5) X(32,6, 9) \
	/* g33 Frozen Analog Input Event  (A.17) */			\
	X(33,0,ANY) X(33,1, 5) X(33,2, 3) X(33,3,11) X(33,4, 9) X(33,5, 5) X(33,6, 9) \
	/* g40 Analog Output Status       (A.19) */			\
	X(40,0,ANY) X(40,1, 5) X(40,2, 3) X(40,3, 5)			\
	/* g41 Analog Output Command      (A.20) */			\
	X(41,1, 5) X(41,2, 3) X(41,3, 5)				\
	/* g42 Analog Output Event        (A.21) */			\
	X(42,0,ANY) X(42,1, 5) X(42,2, 3) X(42,3,11) X(42,4, 9) X(42,5, 5) X(42,6, 9) \
	/* g50 Time and Date              (A.23) */			\
	X(50,1, 6) X(50,2,10) X(50,3, 6) X(50,4,11)			\
	/* g51 Time and Date CTO          (A.24) */			\
	X(51,1, 6) X(51,2, 6)						\
	/* g52 Time Delay                 (A.25) */			\
	X(52,1, 2) X(52,2, 2)						\
	/* g60 Class Data                 (A.26: carries no data) */	\
	X(60,1,ANY) X(60,2,ANY) X(60,3,ANY) X(60,4,ANY)			\
	/* g80 Internal Indications       (A.28) */			\
	X(80,1,PKD)

static const u8 DNP3_POINT_SIZE[81][7] = {
#define X(g, v, sz)	[g][v] = (u8)(sz),
	DNP3_POINTS(X)
#undef X
};

#undef PKD
#undef ANY

/* Range size by qualifier low nibble (index = qualifier & 0x0F, max 15). */
static const u8 DNP3_RANGE_SIZE[16] = {
	0x02,
	0x04,
	0x08,
	0xFF,
	0xFF,
	0xFF,
	0x00,
	0x01,
	0x02,
	0xFF,
	0xFF,
	0xFF,
	0xFF,
	0xFF,
	0xFF,
	0xFF,
};

/* Prefix size by qualifier bits 4-6 (index = (qualifier>>4)&7, max 7). */
static const u8 DNP3_PREFIX_SIZE[8] = {
	0x00,
	0x01,
	0x02,
	0x04,
	0xFF,
	0xFF,
	0xFF,
	0xFF
};

/*@
requires // that message size is limited
	length <= 65535;

requires // that the apdu is empty or readable
	length == 0 ||
	\valid_read(apdu + (0 .. length - 1));

assigns
	\nothing;	// Pure function: no memory is modified

ensures	// that under/oversize messages are always rejected
	apdu != \null &&
	(length < SAFE_DNP3_MIN_APP || length > SAFE_DNP3_MAX_APP)
		==> \result.error == DNP3_REJECT_SIZE;

ensures // that function code not in whitelist is always rejected
	apdu			!= \null				&&
	length			>= SAFE_DNP3_MIN_APP			&&
	length			<= SAFE_DNP3_MAX_APP			&&
	apdu[1]		< sizeof(DNP3_FUNCTION_CODE_WHITELIST)	&&
	DNP3_FUNCTION_CODE_WHITELIST[apdu[1]] == 0
		==> \result.error == DNP3_REJECT_FUNCTION_CODE;

ensures // that accepted messages have at most 64 object headers
	\result.error == DNP3_OK
		==> \result.object_count <= SAFE_DNP3_MAX_OBJECTS;
*/
SAFE_PURE SafeDnp3Result safe_dnp3_filter (
	const	u8	*const	apdu,
	const	u32	length
)
{
	SafeDnp3Result out = {
				.error		= DNP3_OK,
				.reject_at	= 0U,
				.function_code	= 0U,
				.object_count	= 0U
	};

	if (length < SAFE_DNP3_MIN_APP || length > SAFE_DNP3_MAX_APP) {
		return_filter (DNP3_REJECT_SIZE,0U);
	}

	u32 offset = 1U;

	out.function_code = apdu[offset++];

	/* Function code whitelist */

	if (
		out.function_code >= sizeof(DNP3_FUNCTION_CODE_WHITELIST) ||
		! DNP3_FUNCTION_CODE_WHITELIST[out.function_code]
	) {
		return_filter (DNP3_REJECT_FUNCTION_CODE,PREVIOUS(offset));
	}

	/*@
		assert
			out.function_code < sizeof(DNP3_FUNCTION_CODE_WHITELIST)
				&&
			DNP3_FUNCTION_CODE_WHITELIST[out.function_code] != 0;
	*/

	/* Confirm and delay-measure have no objects */
	if (out.function_code == DNP3_FC_CONFIRM || out.function_code == DNP3_FC_DELAY_MEASURE) {
		return out;
	}

	/* Response: skip 2-byte IIN */
	if (out.function_code >= DNP3_RESPONSE_BIT)
	{
		const U32 iin_end = ADD(offset, 2U);

		if (iin_end.overflowed || iin_end.value > length) {
			return_filter (DNP3_REJECT_TRUNCATE,offset);
		}

		offset = iin_end.value;
	}

	u32 object_count = 0U;

	/*@
		loop invariant
				0 <= object_count <= SAFE_DNP3_MAX_OBJECTS;

		loop invariant
				offset <= length;

		loop assigns
				object_count,
				offset,
				out;

		loop variant
				(int)(SAFE_DNP3_MAX_OBJECTS - object_count);
	*/
	while (offset < length)
	{
		if (object_count >= SAFE_DNP3_MAX_OBJECTS)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_OBJ_COUNT,offset);
		}

		const U32 ohdr_end = ADD(offset, 3U);

		if (ohdr_end.overflowed || ohdr_end.value > length)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_TRUNCATE,offset);
		}

		const u8 group		= apdu[offset++];
		const u8 variation	= apdu[offset++];
		const u8 qualifier	= apdu[offset++];

		const U32 group_pos	= SUBTRACT(offset, 3U);
		const U32 var_pos	= SUBTRACT(offset, 2U);

		/* Group whitelist */
		if (
			group >= sizeof(DNP3_GROUP_WHITELIST) ||
			! DNP3_GROUP_WHITELIST[group]
		) {
			out.object_count = object_count;
			return_filter (DNP3_REJECT_GROUP,group_pos.underflowed ? 0U : group_pos.value);
		}

		if (group >= (sizeof(DNP3_POINT_SIZE)/sizeof(DNP3_POINT_SIZE[0])))
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_GROUP,group_pos.underflowed ? 0U : group_pos.value);
		}

		/*
			@ assert
				group < sizeof(DNP3_GROUP_WHITELIST) &&
				DNP3_GROUP_WHITELIST[group] != 0;
		*/

		if (variation >= 7U) /* Variation: 2D lookup */
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_VARIATION,var_pos.underflowed ? 0U : var_pos.value);
		}

		const u8 point_size = DNP3_POINT_SIZE[group][variation];

		if (point_size == DNP3_VARIATION_INVALID)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_VARIATION,var_pos.underflowed ? 0U : var_pos.value);
		}

		/* Qualifier: range size + prefix size lookups */

		/* Qualifier bit 7 is reserved (IEEE 1815) and shall be zero. */
		if ((qualifier & 0x80U) != 0U)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_QUALIFIER,PREVIOUS(offset));
		}

		const u8 range_size = DNP3_RANGE_SIZE[qualifier & 0x0FU];

		if (range_size == 0xFFU)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_QUALIFIER,PREVIOUS(offset));
		}

		const u8 prefix_size = DNP3_PREFIX_SIZE[(qualifier >> 4) & 0x07U];

		if (prefix_size == 0xFFU)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_QUALIFIER,PREVIOUS(offset));
		}

		const U32 rng_end = ADD(offset, (u32)range_size);

		if (rng_end.overflowed || rng_end.value > length)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_TRUNCATE,offset);
		}

		const u8 *range_buffer = &apdu[offset];

		offset = rng_end.value;

		/* Point count from range field, then advance past data */

		u32 count = 0U;

		switch (qualifier & 0x0FU)
		{
			case 0x00: /* 1-byte start-stop */
			{
				if (range_size >= 2)
				{
					if (range_buffer[1] < range_buffer[0])
					{
						/* inverted range (start > stop) is malformed */
						out.object_count	= object_count;
						return_filter (DNP3_REJECT_OBJ_COUNT,offset);
					}

					count = 1U + (u32) (
						range_buffer[1] - range_buffer[0]
					);
				}

				break;
			}

			case 0x01: /* 2-byte start-stop */
			{
				if (range_size >= 4)
				{
					const u32 range_start = (
						(u32) range_buffer[0] |
						((u32)range_buffer[1] << 8)
					);

					const u32 range_end = (
						(u32) range_buffer[2] |
						((u32)range_buffer[3] << 8)
					);

					if (range_end < range_start)
					{
						/* inverted range (start > stop) is malformed */
						out.object_count	= object_count;
						return_filter (DNP3_REJECT_OBJ_COUNT,offset);
					}

					const U32 range_diff = SUBTRACT(range_end, range_start);

					/* 2-byte range: max diff is 65535, +1 = 65536 - no u32 overflow possible */
					const U32 Count = range_diff.underflowed ?
								(U32){0,0,0}:
								ADD(range_diff.value, 1U);

					count = Count.value;
				}

				break;
			}

			case 0x02: /* 4-byte start-stop */
			{
				if (range_size >= 8U)
				{
					const u32 range_start = (
						(u32) range_buffer[0]		|
						((u32)range_buffer[1] << 8U)	|
						((u32)range_buffer[2] << 16U)	|
						((u32)range_buffer[3] << 24U)
					);

					const u32 range_end = (
						(u32) range_buffer[4]		|
						((u32)range_buffer[5] << 8U)	|
						((u32)range_buffer[6] << 16U)	|
						((u32)range_buffer[7] << 24U)
					);

					if (range_end < range_start)
					{
						/* inverted range (start > stop) is malformed */
						out.object_count = object_count;
						return_filter (DNP3_REJECT_OBJ_COUNT,offset);
					}

					const U32 range_diff = SUBTRACT(range_end, range_start);

					if (range_diff.underflowed)
					{
						out.object_count = object_count;
						return_filter (DNP3_REJECT_TRUNCATE,offset);
					}

					const U32 Count = ADD(range_diff.value, 1U);

					if (Count.overflowed)
					{
						out.object_count = object_count;
						return_filter (DNP3_REJECT_TRUNCATE,offset);
					}

					count = Count.value;
				}

				break;
			}

			case 0x06: /* no range (all objects) */
				break;

			case 0x07: /* 1-byte count */
			{
				if (range_size >= 1) {
					count = (u32)range_buffer[0];
				}

				break;
			}

			case 0x08: /* 2-byte count */
			{
				if (range_size >= 2)
				{
					count = (u32) range_buffer[0] |
						((u32)range_buffer[1] << 8);
				}

				break;
			}

			default:
				break;
		}

		/* Guard: count > length is impossible for valid data (each point >= 1 byte)
		 * and prevents overflow in count+7, count*size, and offset+data_bytes. */
		if (count > length)
		{
			out.object_count = object_count;
			return_filter (DNP3_REJECT_TRUNCATE,offset);
		}

		const int is_read = (
				out.function_code == DNP3_FC_READ             ||
				out.function_code == DNP3_FC_ASSIGN_CLASS     ||
				out.function_code == DNP3_FC_ENABLE_UNSOLICITED  ||
				out.function_code == DNP3_FC_DISABLE_UNSOLICITED
		);

		if (! is_read && point_size != DNP3_VARIATION_ANY && count > 0U)
		{
			u32 data_bytes;

			if (point_size == DNP3_VARIATION_PACKED)
			{
				const U32 packed = ADD(count, 7U);

				if (packed.overflowed)
				{
					out.object_count = object_count;
					return_filter (DNP3_REJECT_TRUNCATE,offset);
				}

				data_bytes = packed.value / 8U;
			}
			else
			{
				data_bytes = count * (
					(u32) point_size + (u32) prefix_size
				);
			}

			const U32 dat_end = ADD(offset, data_bytes);

			if (dat_end.overflowed || dat_end.value > length)
			{
				out.object_count = object_count;
				return_filter (DNP3_REJECT_TRUNCATE,offset);
			}

			offset = dat_end.value;
		}

		++object_count;
	}

	out.object_count = object_count;

	return out;
}

/* ==========================================================
 * SafeGOOSE - State transition table filter
 * ========================================================== */

#define GOOSE_STATE_REJECT	0U
#define GOOSE_STATE_ACCEPT	13U
#define GOOSE_STATE_COUNT	14U

static const u8 GOOSE_NEXT_STATE[GOOSE_STATE_COUNT][256] = {

	[ 1] = { [0x80] =	2 },
	[ 2] = { [0x81] =	3 },
	[ 3] = { [0x82] =	4 },
	[ 4] = { [0x83] =	5, [0x84] = 6 },	/* goID optional */
	[ 5] = { [0x84] =	6 },
	[ 6] = { [0x85] =	7 },
	[ 7] = { [0x86] =	8 },
	[ 8] = { [0x87] =	9 },
	[ 9] = { [0x88] =	10 },
	[10] = { [0x89] =	11 },
	[11] = { [0x8A] =	12 },
	[12] = { [0xAB] =	GOOSE_STATE_ACCEPT },
};

typedef struct
{
	u16 min;
	u16 max;

} GooseFieldBounds;

static const GooseFieldBounds GOOSE_FIELD_BOUNDS[256] = {
	/*		min,	max	*/
	[0x80] = {	1,	129	},	/* gocbRef		*/
	[0x81] = {	1,	5	},	/* timeAllowedToLive	*/
	[0x82] = {	1,	129	},	/* datSet		*/
	[0x83] = {	1,	65	},	/* goID (IEC 61850-8-1: VisibleString SIZE(1..65)) */
	[0x84] = {	8,	8	},	/* t (UTC time)		*/
	[0x85] = {	1,	5	},	/* stNum		*/
	[0x86] = {	1,	5	},	/* sqNum		*/
	[0x87] = {	1,	1	},	/* simulation		*/
	[0x88] = {	1,	5	},	/* confRev		*/
	[0x89] = {	1,	1	},	/* ndsCom		*/
	[0x8A] = {	1,	5	},	/* numDatSetEntries	*/
	[0xAB] = {	0,	1400	},	/* allData		*/
};

static const u8 GOOSE_DATA_VALUE_WHITELIST[168] = {

	[0x83] = 1,	/* boolean		*/
	[0x84] = 1,	/* bit-string		*/
	[0x85] = 1,	/* integer		*/
	[0x86] = 1,	/* unsigned		*/
	[0x87] = 1,	/* floating-point	*/
	[0x89] = 1,	/* octet-string		*/
	[0x8A] = 1,	/* visible-string	*/

#ifdef SAFE_ENABLE_GOOSE_MMS_STRING
	[0x90] = 1,	/* mms-string		*/
#endif

	[0x91] = 1,	/* utc-time		*/

	[0xA1] = 1,	/* array		*/
	[0xA2] = 1,	/* structure		*/
};

/*@
requires // that buffer is empty or readable
	length == 0 ||
	\valid_read(content + (0 .. length - 1));

requires // that output pointers are valid
	\valid(reject_offset);

requires
	\valid(data_value_count_output);

requires // that output pointers do not alias each other or the content buffer
	\separated(reject_offset, data_value_count_output);

requires
	\separated(reject_offset, content + (0 .. length - 1));

requires
	\separated(data_value_count_output, content + (0 .. length - 1));

requires // Maximum allData size
	length <= SAFE_GOOSE_MAX_APDU;

requires // nesting depth is within the configured limit
	depth <= SAFE_GOOSE_MAX_DATA_DEPTH;

decreases // termination measure: remaining depth scaled by remaining bytes
	(SAFE_GOOSE_MAX_DATA_DEPTH - depth) * (SAFE_GOOSE_MAX_APDU + 1U) + length;

// Only output pointers are modified
assigns
	*reject_offset,
	*data_value_count_output;

ensures // that data value count is bounded on all paths
	*data_value_count_output <= SAFE_GOOSE_MAX_DATA_VALUES;
*/
static u32 goose_validate_alldata (
	const	u8		*const	content,
	const	u32		length,
		u32	*const	reject_offset,
		u32	*const	data_value_count_output,
	const	u32		depth
)
{
	u32 offset = 0U;
	u32 count  = 0U;

	/*@
		loop invariant
				offset <= length;

		loop invariant
				count <= SAFE_GOOSE_MAX_DATA_VALUES;

		loop assigns
				offset,
				count,
				*reject_offset,
				*data_value_count_output;

		loop variant
				length - offset;
	*/
	while (offset < length)
	{
		/*@ ghost u32 offset_top = offset; */

		if (count >= SAFE_GOOSE_MAX_DATA_VALUES)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_COUNT;
		}

		/*@ assert offset < length; */

		const u8 value_tag = content[offset++];

		if (
			value_tag >= sizeof(GOOSE_DATA_VALUE_WHITELIST) ||
			! GOOSE_DATA_VALUE_WHITELIST[value_tag]
		)
		{
			*reject_offset			= PREVIOUS(offset);
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_TAG;
		}

		/*@
			assert
				value_tag < sizeof(GOOSE_DATA_VALUE_WHITELIST) &&
				GOOSE_DATA_VALUE_WHITELIST[value_tag] != 0;
		*/

		/*@ assert offset > offset_top; */

		/* Inline BER length decode */

		if (offset >= length)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_TRUNCATE;
		}

		const	u8	length_byte	= content[offset++];
			u32	value_len	= 0U;

		if ((length_byte & BER_LONG_FORM_BIT) == 0U)
		{
			value_len = (u32) length_byte;
		}
		else
		{
			const u32 num_length_bytes = (u32) (
						length_byte & BER_LENGTH_MASK
			);

			if (num_length_bytes > 4U)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_TRUNCATE;
			}

			const U32 Bytes_Required = ADD(offset, num_length_bytes);

			if (Bytes_Required.overflowed || Bytes_Required.value > length)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_TRUNCATE;
			}

			/*@
				loop invariant
						0 <= i <= num_length_bytes;

				loop invariant
						offset <= length;
				loop invariant
						offset > offset_top;

				loop assigns
						i,
						value_len,
						offset;

				loop variant
						num_length_bytes - i;
			*/
			for (
				u32 i = 0U;
				(i < num_length_bytes) && (offset < length);
				++i
			)
			{
				value_len = (value_len << 8U) | (u32) content[offset++];
			}
		}

		/*@ assert offset > offset_top; */

		const U32 Value_End = ADD(offset, value_len);

		if (Value_End.overflowed || Value_End.value > length)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_TRUNCATE;
		}

		/* array/structure: recurse into inner data values */
		if (
			value_tag == GOOSE_DATA_ARRAY_TAG	||
			value_tag == GOOSE_DATA_STRUCTURE_TAG
		)
		{
			if (depth >= SAFE_GOOSE_MAX_DATA_DEPTH)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_DATA_VALUE_TAG;
			}

			const U32 Next_Depth	= ADD(depth, 1U);

			if (Next_Depth.overflowed)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_DATA_VALUE_TAG;
			}

			u32 inner_reject	= 0U;
			u32 inner_count		= 0U;

			const u32 inner_error = goose_validate_alldata (
								content + offset,
								value_len,
								&inner_reject,
								&inner_count,
								Next_Depth.value
			);

			if (inner_error != 0U)
			{
				const U32 Reject_Sum		= ADD(offset, inner_reject);

				*reject_offset			= Reject_Sum.overflowed ? offset : Reject_Sum.value;
				*data_value_count_output	= count;

				return inner_error;
			}

			/* A structure/array is ONE AllData entry (IEC 61850-8-1 S9.2.1:
			 * numDatSetEntries counts top-level entries). Its children are
			 * validated by the recursion above; their count does not propagate
			 * to the top-level entry total. The container is counted by the
			 * ++count below, like any other top-level value. */
			(void) inner_count;
		}

		/* GOOSE bit-string (tag 0x84): validate unused-bits byte and max size.
		 * IEC 61850-8-1 bit-strings carry at most 7 padding bits;
		 * a value > 7 is malformed per the BIT STRING encoding rules.
		 * Max size is 1016 bits per Table A.2: 1 unused-bits byte + 127 data bytes. */
		if (value_tag == GOOSE_DATA_BIT_STRING_TAG)
		{
			if (value_len < 1U || content[offset] > SAFE_GOOSE_BITSTRING_MAX_UNUSED_BITS)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_DATA_VALUE_PADDING;
			}

			if (value_len > SAFE_GOOSE_MAX_BIT_STRING)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_DATA_VALUE_LENGTH;
			}
		}

		/* Per-type length checks per IEC 61850-8-1 Annex A.3, Table A.2 */

		if (value_tag == GOOSE_DATA_BOOLEAN_TAG && value_len != SAFE_GOOSE_BOOLEAN_LENGTH)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}

		if (value_tag == GOOSE_DATA_FLOAT_TAG && value_len != SAFE_GOOSE_FLOAT_LENGTH)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}

		if (value_tag == GOOSE_DATA_TIMESTAMP_TAG && value_len != SAFE_GOOSE_TIMESTAMP_LENGTH)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}

		if (value_tag == GOOSE_DATA_OCTET_STRING_TAG && value_len > SAFE_GOOSE_MAX_OCTET_STRING)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}

		if (value_tag == GOOSE_DATA_VISIBLE_STRING_TAG && value_len > SAFE_GOOSE_MAX_VISIBLE_STRING)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}

#ifdef SAFE_ENABLE_GOOSE_MMS_STRING
		if (value_tag == GOOSE_DATA_MMS_STRING_TAG && value_len > SAFE_GOOSE_MAX_MMS_STRING)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}
#endif

		if (
			value_tag == GOOSE_DATA_INTEGER_TAG &&
			(value_len == 0U || value_len > SAFE_GOOSE_MAX_INTEGER_LENGTH)
		)
		{
			*reject_offset			= offset;
			*data_value_count_output	= count;

			return GOOSE_REJECT_DATA_VALUE_LENGTH;
		}

		if (value_tag == GOOSE_DATA_UNSIGNED_TAG)
		{
			if (value_len == 0U || value_len > SAFE_GOOSE_MAX_UNSIGNED_LENGTH)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_DATA_VALUE_LENGTH;
			}

			/* INT32U value subset [0, 2^32-1]: reject negatives
			 * (BER sign bit set) and magnitudes above 0xFFFFFFFF.
			 * A 5-byte encoding must lead with 0x00, which is
			 * non-negative and caps the magnitude at 0xFFFFFFFF.
			 * Minimal-encoding is NOT enforced (interop). */
			if (value_len == SAFE_GOOSE_MAX_UNSIGNED_LENGTH)
			{
				if (content[offset] != 0x00U)
				{
					*reject_offset			= offset;
					*data_value_count_output	= count;

					return GOOSE_REJECT_DATA_VALUE_RANGE;
				}
			}
			else if ((content[offset] & BER_SIGN_BIT) != 0U)
			{
				*reject_offset			= offset;
				*data_value_count_output	= count;

				return GOOSE_REJECT_DATA_VALUE_RANGE;
			}
		}

		offset = Value_End.value;

		/*@ assert offset > offset_top; */

		++count;
	}

	if (count < 1U)
	{
		*reject_offset			= offset;
		*data_value_count_output	= 0U;

		return GOOSE_REJECT_DATA_VALUE_COUNT;
	}

	*data_value_count_output = count;

	return 0U;
}

/*@
requires // that message length is limited
	length <= 65535;

requires // that ethernet_frame is empty or readable
	length == 0 ||
	\valid_read(ethernet_frame + (0 .. length - 1));

assigns
	\nothing;

ensures // that accepted frames have at most 64 data values (all paths)
	\result.error == GOOSE_OK
		==> \result.data_value_count <= SAFE_GOOSE_MAX_DATA_VALUES;

behavior undersized:
	assumes length < GOOSE_MIN_FRAME;
	ensures \result.error == GOOSE_REJECT_SIZE;

behavior without_vlan:
	assumes length >= GOOSE_MIN_FRAME;
	assumes length <  GOOSE_MIN_FRAME + 4 ||
		ethernet_frame[ETH_ETHERTYPE_OFFSET    ] != VLAN_TPID_HI ||
		ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] != VLAN_TPID_LO;
	ensures
		(ethernet_frame[ETH_ETHERTYPE_OFFSET    ] != GOOSE_ETHERTYPE_HI ||
		 ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] != GOOSE_ETHERTYPE_LO)
			==> \result.error == GOOSE_REJECT_ETH_TYPE;

behavior with_vlan:
	assumes length >= GOOSE_MIN_FRAME + 4;
	assumes ethernet_frame[ETH_ETHERTYPE_OFFSET    ] == VLAN_TPID_HI;
	assumes ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] == VLAN_TPID_LO;
	ensures
		(ethernet_frame[ETH_ETHERTYPE_OFFSET + 4] != GOOSE_ETHERTYPE_HI ||
		 ethernet_frame[ETH_ETHERTYPE_OFFSET + 5] != GOOSE_ETHERTYPE_LO)
			==> \result.error == GOOSE_REJECT_ETH_TYPE;

complete
	behaviors undersized, without_vlan, with_vlan;
disjoint
	behaviors undersized, without_vlan, with_vlan;
*/
SAFE_PURE SafeGooseResult safe_goose_filter (
	const	u8	*const	ethernet_frame,
	const	u32		length
)
{
	SafeGooseResult out = {
				.error			= GOOSE_OK,
				.reject_at		= 0U,
				.field			= 0U,
				.data_value_count	= 0U
	};

	if (length < GOOSE_MIN_FRAME) {
		return_filter (GOOSE_REJECT_SIZE,0U);
	}

	/*
		Detect and strip IEEE 802.1Q VLAN tag if present.
		A VLAN-tagged frame has TPID 0x8100 at bytes 12-13;
		the inner EtherType then appears at bytes 16-17.
		We shift the view by 4 bytes so the rest of the function
		sees a normal Ethernet layout (EtherType at offset 12).
	*/

	const int is_vlan_packet = (
		length						>= (GOOSE_MIN_FRAME + 4U)	&&
		ethernet_frame[ETH_ETHERTYPE_OFFSET	]	== VLAN_TPID_HI			&&
		ethernet_frame[ETH_ETHERTYPE_OFFSET + 1U]	== VLAN_TPID_LO
	);

	const	u8	*const	frame		= is_vlan_packet ? (ethernet_frame	+ 4U)	: ethernet_frame;
	const	u32		frame_length	= is_vlan_packet ? (length		- 4U)	: length;

	/* Help WP discharge without_vlan_ensures / with_vlan_ensures:
	 * materialise the two cases for 'frame' so the SMT solver does not
	 * have to re-derive them from the ternary operator inside each behavior. */

	/*@ assert !is_vlan_packet ==> frame == ethernet_frame;		*/
	/*@ assert  is_vlan_packet ==> frame == ethernet_frame + 4;	*/

	/*@ assert frame_length >= GOOSE_MIN_FRAME; */
	if (
		frame[ETH_ETHERTYPE_OFFSET	] != GOOSE_ETHERTYPE_HI ||
		frame[ETH_ETHERTYPE_OFFSET + 1U	] != GOOSE_ETHERTYPE_LO
	) {
		return_filter (GOOSE_REJECT_ETH_TYPE,ETH_ETHERTYPE_OFFSET);
	}

	const u32 goose_len = (
		((u32)frame[PROTOCOL_HEADER_LENGTH_OFFSET	] << 8) |
		(u32) frame[PROTOCOL_HEADER_LENGTH_OFFSET + 1U	]
	);

	const U32 goose_frame_end = ADD(ETH_HEADER_LENGTH, goose_len);

	if (goose_frame_end.overflowed || goose_frame_end.value > frame_length) {
		return_filter (GOOSE_REJECT_HEADER_LENGTH,PROTOCOL_HEADER_LENGTH_OFFSET);
	}

	const U32 APDU_Len = SUBTRACT(frame_length, APDU_OFFSET);

	if (APDU_Len.underflowed) {
		return_filter (GOOSE_REJECT_SIZE,0U);
	}

#ifndef SAFE_IGNORE_RESERVED_GOOSE
	/* Reserved1/Reserved2 validation (IEC 61850-8-1 Fig C.5).
	 * frame_length >= APDU_OFFSET (22) here, so RESERVED1/RESERVED2
	 * (offsets 18-21) are within the frame. All Reserved-field checks below
	 * are skipped when SAFE_IGNORE_RESERVED_GOOSE is defined (e.g. IEC 62351-6
	 * secured GOOSE, which populates the Reserved Security field). */

	/* Reserved1 bit 0: S (simulated). An operational filter rejects simulated
	 * frames, mirroring the APDU-level test field (GOOSE_REJECT_TEST). */
	if ((frame[RESERVED1_OFFSET] & SIM_BIT_MASK) == SIM_BIT_MASK) {
		return_filter (GOOSE_REJECT_SIM,RESERVED1_OFFSET);
	}

	/* Reserved1 bits 1-3: R, shall be 0 (IEC 61850-8-1). */
	if ((frame[RESERVED1_OFFSET] & RESERVED_R_MASK) != 0x00U) {
		return_filter (GOOSE_REJECT_RESERVED,RESERVED1_OFFSET);
	}

	/* Reserved Security field (Reserved1 bits 4-15 + Reserved2): shall be 0 for
	 * unsecured GOOSE (IEC 62351-6 populates it when security is used). */
	if (
		(frame[RESERVED1_OFFSET		] & RESERVED_SEC_MASK)	!= 0x00U ||
		 frame[RESERVED1_OFFSET + 1U	]			!= 0x00U ||
		 frame[RESERVED2_OFFSET		]			!= 0x00U ||
		 frame[RESERVED2_OFFSET + 1U	]			!= 0x00U
	) {
		return_filter (GOOSE_REJECT_RESERVED,RESERVED1_OFFSET);
	}
#endif

	const u32 apdu_len = APDU_Len.value;

	if (apdu_len > SAFE_GOOSE_MAX_APDU) {
		return_filter (GOOSE_REJECT_SIZE,0U);
	}

	const u8 *apdu = frame + APDU_OFFSET;

	if (apdu_len == 0U || apdu[0] != GOOSE_OUTER_TAG) {
		return_filter (GOOSE_REJECT_OUTER_TAG,APDU_OFFSET);
	}

	u32 offset = 1U;

	/*@
		assert
			offset <= apdu_len;
	*/

	/*@
		assert
			\separated(&offset, apdu + (0 .. apdu_len - 1));
	*/

	const U32 body_len_R = read_length(apdu, apdu_len, &offset);
	if (body_len_R.overflowed) {
		return_filter (GOOSE_REJECT_TRUNCATE,APDU_OFFSET + offset);
	}
	const u32 body_len = body_len_R.value;

	/*@ assert offset <= apdu_len; */

	const U32 Body_End = ADD(offset, body_len);

	if (Body_End.overflowed || Body_End.value > apdu_len) {
		return_filter (GOOSE_REJECT_TRUNCATE,APDU_OFFSET + offset);
	}

	const	u32	body_end		= Body_End.value;

		u8	state			= 1U;
		u32	data_value_count	= 0U;
		u32	declared_nde		= 0U;	/* numDatSetEntries declared value */

	/*@
		loop invariant
				offset <= apdu_len;

		loop invariant
				body_end <= apdu_len;

		loop invariant
				0 <= state <= GOOSE_STATE_ACCEPT;

		loop invariant
				data_value_count <= SAFE_GOOSE_MAX_DATA_VALUES;

		loop assigns
				offset,
				state,
				data_value_count,
				declared_nde,
				out;

		loop variant
				body_end - offset;
	*/
	while (offset < body_end && state != GOOSE_STATE_ACCEPT)
	{
		/*@ assert offset < apdu_len; */

		/* Ghost: capture offset at start of this iteration.
		 * Used to prove loop_variant_decrease and terminates_part2:
		 * fld_end.value > offset_top, so body_end - offset decreases. */

		/*@ ghost u32 offset_top = offset; */

		const u8 tag = apdu[offset];

		if (state >= GOOSE_STATE_COUNT) {
			return_filter (GOOSE_REJECT_FIELD_TAG,APDU_OFFSET + offset);
		}

		const u8 next = GOOSE_NEXT_STATE[state][tag];

		if (next == GOOSE_STATE_REJECT)
		{
			out.field = state - 1U;
			return_filter (GOOSE_REJECT_FIELD_TAG,APDU_OFFSET + offset);
		}

		/*
		* All GOOSE_NEXT_STATE entries are in [0, GOOSE_STATE_ACCEPT].
		* This guard is never triggered; it exists so WP can bound 'next'
		* and discharge the loop invariant: 0 <= state <= GOOSE_STATE_ACCEPT.
		*/
		if (next > GOOSE_STATE_ACCEPT) {
			return_filter (GOOSE_REJECT_FIELD_TAG,APDU_OFFSET + offset);
		}

		++offset;

		/*@ assert offset >  offset_top;    */  /* tag byte consumed: strict increase */
		/*@ assert offset <= apdu_len;      */

		/*@ assert
			\separated(&offset, apdu + (0 .. apdu_len - 1));
		*/

		const U32 field_len_R = read_length(apdu, apdu_len, &offset);
		if (field_len_R.overflowed) {
			out.field = state - 1U;
			return_filter (GOOSE_REJECT_TRUNCATE,APDU_OFFSET + offset);
		}
		const u32 field_len = field_len_R.value;

		/*@ assert offset >= offset_top + 1U; */  /* read_length never moves backward */
		/*@ assert offset <= apdu_len;         */

		const U32 fld_end = ADD(offset, field_len);

		if (fld_end.overflowed || fld_end.value > apdu_len)
		{
			out.field = state - 1U;
			return_filter (GOOSE_REJECT_TRUNCATE,APDU_OFFSET + offset);
		}

		/* After this point: fld_end is valid and within bounds.
		 * fld_end.value = offset + field_len >= offset_top + 1 > offset_top,
		 * so body_end - fld_end.value < body_end - offset_top (variant strictly decreases). */
		/*@ assert !fld_end.overflowed;          */
		/*@ assert fld_end.value <= apdu_len;    */
		/*@ assert fld_end.value > offset_top;   */

		/* allData field: validate data values */
		if (state == 12U)
		{
			u32 validation_offset = 0U;

			const u32 validation_result = goose_validate_alldata (
								apdu + offset,
								field_len,
								&validation_offset,
								&data_value_count,
								0U
			);

			/*@ assert
				data_value_count <= SAFE_GOOSE_MAX_DATA_VALUES;
			*/

			if (validation_result != 0U)
			{
				const U32 Reject_a = ADD(APDU_OFFSET, offset);

				const U32 Reject_b = Reject_a.overflowed?
							Reject_a:
							ADD(Reject_a.value, validation_offset);

				out.data_value_count	= data_value_count;
				return_filter (validation_result,Reject_b.overflowed ? APDU_OFFSET : Reject_b.value);
			}

			/* IEC 61850-8-1 S9.2.1: numDatSetEntries must equal
			 * the actual count of AllData entries. */
			if (declared_nde != data_value_count)
			{
				out.data_value_count = data_value_count;
				return_filter (GOOSE_REJECT_DATA_VALUE_COUNT,APDU_OFFSET + offset);
			}
		}
		else
		{
			/* Field size bounds check */

			if (
				field_len > (u32)GOOSE_FIELD_BOUNDS[tag].max ||
				field_len < (u32)GOOSE_FIELD_BOUNDS[tag].min
			) {
				out.field	= state - 1U;
				return_filter (GOOSE_REJECT_FIELD_SIZE,APDU_OFFSET + offset);
			}

			/* Unsigned32 value-range check (IEC 61850-7-2 INT32U):
			 * timeAllowedToLive 0x81, stNum 0x85, sqNum 0x86,
			 * confRev 0x88, numDatSetEntries 0x8A. The size bounds
			 * above accept byte-lengths 1..5; tighten to the value
			 * subset [0, 2^32-1] so a 5-byte BER integer cannot encode
			 * a negative (sign bit set) or a magnitude above 0xFFFFFFFF.
			 * A 5-byte encoding must lead with 0x00, which is
			 * simultaneously non-negative and caps the magnitude at
			 * 0xFFFFFFFF. Minimal-encoding is NOT enforced (zero-padding
			 * IED interop). */
			if (
				tag == 0x81U || tag == 0x85U || tag == 0x86U ||
				tag == 0x88U || tag == 0x8AU
			)
			{
				/* bounds check above ensures field_len >= 1,
				 * so offset < apdu_len. */
				/*@ assert field_len >= 1U;   */
				/*@ assert offset < apdu_len; */

				if (field_len == 5U)
				{
					if (apdu[offset] != 0x00U) {
						out.field	= state - 1U;
						return_filter (GOOSE_REJECT_FIELD_VALUE,APDU_OFFSET + offset);
					}
				}
				else if ((apdu[offset] & BER_SIGN_BIT) != 0U) {
					out.field	= state - 1U;
					return_filter (GOOSE_REJECT_FIELD_VALUE,APDU_OFFSET + offset);
				}
			}

			/* numDatSetEntries (0x8A): decode declared count for later
			 * comparison against the actual AllData entry count.
			 * BER unsigned integer, big-endian, 1-5 bytes
			 * (IEC 61850-8-1 S9.2.1, IMPLICIT [10] UNSIGNED32). */
			if (tag == 0x8AU)
			{
				/* offset + field_len == fld_end.value <= apdu_len,
				 * so apdu[offset + i] is valid for all i < field_len. */
				/*@ assert offset + field_len == fld_end.value; */

				declared_nde = 0U;

				/*@
					loop invariant 0 <= i <= field_len;
					loop invariant fld_end.value <= apdu_len;
					loop assigns i, declared_nde;
					loop variant field_len - i;
				*/
				for (u32 i = 0U; i < field_len; i++)
				{
					/*@ assert offset + i < apdu_len; */
					declared_nde = (declared_nde << 8) | (u32)apdu[offset + i];
				}
			}

			/* test field (0x87): reject GOOSE frames in test/simulation mode.
			 * BER BOOLEAN: any non-zero byte is TRUE per X.690 s11.1.
			 * Protection relays must ignore test=TRUE GOOSE per IEC 61850-8-1.
			 * This check is unconditional: a commissioning tool that needs to
			 * process test frames should not use an operational safety filter. */
			if (tag == 0x87U)
			{
				/* GOOSE_FIELD_BOUNDS[0x87] = {min=1, max=1};
				 * bounds check above ensures field_len >= 1, so offset < apdu_len. */
				/*@ assert field_len >= 1U;    */
				/*@ assert offset < apdu_len;  */

				if (apdu[offset] != 0x00U) {
					out.field	= state - 1U;
					return_filter (GOOSE_REJECT_TEST,APDU_OFFSET + offset);
				}
			}
		}

		offset	= fld_end.value;
		state	= next;
	}

	if (state != GOOSE_STATE_ACCEPT) {
		return_filter (GOOSE_REJECT_FIELD_TAG,APDU_OFFSET + offset);
	}

	out.data_value_count = data_value_count;

	return out;
}

/* ==========================================================
 * SafeSV - Sampled Values filter
 * ========================================================== */

typedef struct
{
	u8		tag;
	u16	max;
	u16	min;
	u8		optional;

} SvField;

static const SvField SV_FIELDS[10] = {
	/* tag,	max,	min,	opt					*/
	{ 0x80,	65,	1,	0 },	/* svID				*/
	{ 0x81,	129,	0,	1 },	/* datSet (optional; ObjectReference, IEC 61850-9-2 Table 14; matches GOOSE datSet 129) */
	{ 0x82,	2,	2,	0 },	/* smpCnt			*/
	{ 0x83,	4,	4,	0 },	/* confRev			*/
	{ 0x84,	8,	8,	1 },	/* refrTm	(optional, SIZE(8) when present)	*/
	{ 0x85,	1,	1,	1 },	/* smpSynch	(optional)	*/
	{ 0x86,	2,	2,	1 },	/* smpRate	(optional, SIZE(2) INT16U)	*/
	{ 0x87,	4096,	1,	0 },	/* data				*/
	{ 0x88,	2,	2,	1 },	/* smpMod	(optional, SIZE(2) INT16U)	*/
	{ 0x89,	8,	8,	1 },	/* gmidData	(optional, undocumented vendor extension; observed SIZE(8), no IEC normative source)	*/
};

/*@
requires // that content buffer is empty or readable
	length == 0 ||
	\valid_read(content + (0 .. length - 1));

requires // that output pointer is valid and does not alias the content buffer
	\valid(reject_offset);

requires
	\separated(reject_offset, content + (0 .. length - 1));

requires // a limit on ASDU size
	length <= 4096;

assigns // only the reject offset is modified
	*reject_offset;
*/
static u32 sv_validate_asdu (
	const	u8		*const	content,
	const	u32		length,
		u32	*const	reject_offset
)
{
	u32 offset      = 0U;
	u32 field_index = 0U;

	/*@
		loop invariant
				offset <= length;

		loop invariant
				field_index <= 10;

		loop assigns
				offset,
				field_index,
				*reject_offset;

		loop variant
				10 - field_index;
	*/
	while ((offset < length) && (field_index < 10U))
	{
		/*@ assert offset < length; */

		if (
			SV_FIELDS[field_index].optional &&
			content[offset] != SV_FIELDS[field_index].tag
		)
		{
			++field_index;
			continue;
		}

		if (content[offset] != SV_FIELDS[field_index].tag)
		{
			*reject_offset = offset;
			return SV_REJECT_FIELD_TAG;
		}

		/*@ assert content[offset] == SV_FIELDS[field_index].tag; */

		++offset;

		if (offset >= length)
		{
			*reject_offset = offset;
			return SV_REJECT_TRUNCATE;
		}

		const u8 length_byte = content[offset++];

		u32 field_len = 0U;

		if ((length_byte & BER_LONG_FORM_BIT) == 0U) {
			field_len = (u32)length_byte;
		}
		else
		{
			const u32 num_length_bytes = (u32) (
				length_byte & BER_LENGTH_MASK
			);

			if (num_length_bytes > 4U)
			{
				*reject_offset = offset;
				return SV_REJECT_TRUNCATE;
			}

			const U32 Bytes_Required = ADD(offset, num_length_bytes);

			if (Bytes_Required.overflowed || Bytes_Required.value > length)
			{
				*reject_offset = offset;
				return SV_REJECT_TRUNCATE;
			}

			/*@
				loop invariant
						0 <= i <= num_length_bytes;

				loop invariant
						offset <= length;

				loop assigns
						i,
						field_len,
						offset;

				loop variant
						num_length_bytes - i;
			*/
			for (
				u32 i = 0U;
				(i < num_length_bytes) && (offset < length);
				++i
			)
			{
				field_len = (field_len << 8U) | (u32)content[offset];
				++offset;
			}
		}

		const U32 asdu_fld_end = ADD(offset, field_len);

		if (asdu_fld_end.overflowed || asdu_fld_end.value > length)
		{
			*reject_offset = offset;
			return SV_REJECT_TRUNCATE;
		}

		if (field_len > (u32)SV_FIELDS[field_index].max)
		{
			*reject_offset = offset;
			return SV_REJECT_FIELD_SIZE;
		}

		if (field_len < (u32)SV_FIELDS[field_index].min)
		{
			*reject_offset = offset;
			return SV_REJECT_FIELD_SIZE;
		}

		/* smpSynch (0x85): INT8U; valid: 0,1,2,5-254; reserved (do not use): 3,4,255 */
		if (SV_FIELDS[field_index].tag == SV_SMPSYNC_TAG && field_len == 1U &&
			(content[offset] == 3U || content[offset] == 4U || content[offset] == 255U))
		{
			*reject_offset = offset;
			return SV_REJECT_CONTENT;
		}

		/* smpMod (0x88): INT16U big-endian, SIZE(2); valid values 0-2 */
		if (SV_FIELDS[field_index].tag == SV_SMPMOD_TAG && field_len == 2U &&
			(content[offset] != 0U || content[offset + 1U] > 2U))
		{
			*reject_offset = offset;
			return SV_REJECT_CONTENT;
		}

		offset = asdu_fld_end.value;

		++field_index;
	}

	/*@
		loop invariant
				field_index <= remaining <= 10;

		loop assigns
				remaining,
				*reject_offset;

		loop variant
				10 - remaining;
	*/
	for (u32 remaining = field_index; remaining < 10U; ++remaining)
	{
		if (! SV_FIELDS[remaining].optional)
		{
			*reject_offset = offset;
			return SV_REJECT_FIELD_TAG;
		}
	}

	/* The safe subset is closed: no trailing / unknown TLVs may follow the
	   recognised fields (the recognised set is SV_FIELDS[]; any other
	   extension tag after them is rejected). */
	if (offset != length)
	{
		*reject_offset = offset;
		return SV_REJECT_TRAILING;
	}

	return 0U;
}

/*@
requires // maximum frame size of
	length <= 65535;

requires // that ethernet_frame is empty or readable
	length == 0 ||
	\valid_read(ethernet_frame + (0 .. length - 1));

assigns
	\nothing;

ensures // that accepted frames have at most 8 ASDUs (all paths)
	\result.error == SV_OK
		==> \result.asdu_count <= SAFE_SV_MAX_ASDU;

behavior bad_size:
	assumes length < SAFE_SV_MIN_FRAME || length > SAFE_SV_MAX_FRAME;
	ensures \result.error == SV_REJECT_SIZE;

behavior without_vlan:
	assumes length >= SAFE_SV_MIN_FRAME;
	assumes length <= SAFE_SV_MAX_FRAME;
	assumes length <  SAFE_SV_MIN_FRAME + 4 ||
		ethernet_frame[ETH_ETHERTYPE_OFFSET    ] != VLAN_TPID_HI ||
		ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] != VLAN_TPID_LO;
	ensures
		(ethernet_frame[ETH_ETHERTYPE_OFFSET    ] != SV_ETHERTYPE_HI ||
		 ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] != SV_ETHERTYPE_LO)
			==> \result.error == SV_REJECT_ETH_TYPE;
	ensures // APPID outside the SV band [0x4000,0x7FFF] is rejected (EtherType matched)
		(ethernet_frame[ETH_ETHERTYPE_OFFSET    ] == SV_ETHERTYPE_HI &&
		 ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] == SV_ETHERTYPE_LO &&
		 (((u32)ethernet_frame[ETH_HEADER_LENGTH] * 256 + (u32)ethernet_frame[ETH_HEADER_LENGTH + 1]) < SV_APPID_MIN ||
		  ((u32)ethernet_frame[ETH_HEADER_LENGTH] * 256 + (u32)ethernet_frame[ETH_HEADER_LENGTH + 1]) > SV_APPID_MAX))
			==> \result.error == SV_REJECT_APPID;

behavior with_vlan:
	assumes length >= SAFE_SV_MIN_FRAME + 4;
	assumes length <= SAFE_SV_MAX_FRAME;
	assumes ethernet_frame[ETH_ETHERTYPE_OFFSET    ] == VLAN_TPID_HI;
	assumes ethernet_frame[ETH_ETHERTYPE_OFFSET + 1] == VLAN_TPID_LO;
	ensures
		(ethernet_frame[ETH_ETHERTYPE_OFFSET + 4] != SV_ETHERTYPE_HI ||
		 ethernet_frame[ETH_ETHERTYPE_OFFSET + 5] != SV_ETHERTYPE_LO)
			==> \result.error == SV_REJECT_ETH_TYPE;
	ensures // APPID outside the SV band [0x4000,0x7FFF] is rejected (EtherType matched, VLAN)
		(ethernet_frame[ETH_ETHERTYPE_OFFSET + 4] == SV_ETHERTYPE_HI &&
		 ethernet_frame[ETH_ETHERTYPE_OFFSET + 5] == SV_ETHERTYPE_LO &&
		 (((u32)ethernet_frame[ETH_HEADER_LENGTH + 4] * 256 + (u32)ethernet_frame[ETH_HEADER_LENGTH + 5]) < SV_APPID_MIN ||
		  ((u32)ethernet_frame[ETH_HEADER_LENGTH + 4] * 256 + (u32)ethernet_frame[ETH_HEADER_LENGTH + 5]) > SV_APPID_MAX))
			==> \result.error == SV_REJECT_APPID;

complete
	behaviors bad_size, without_vlan, with_vlan;
disjoint
	behaviors bad_size, without_vlan, with_vlan;

*/
SAFE_PURE SafeSvResult safe_sv_filter (
	const	u8	*const	ethernet_frame,
	const	u32		length
)
{
	SafeSvResult out = {
				.error		= SV_OK,
				.reject_at	= 0U,
				.asdu_count	= 0U
	};

	if (length > SAFE_SV_MAX_FRAME || length < SAFE_SV_MIN_FRAME) {
		return_filter (SV_REJECT_SIZE,0U);
	}

	/*
		Detect and strip IEEE 802.1Q VLAN tag if present.
		A VLAN-tagged frame has TPID 0x8100 at bytes 12-13;
		the inner EtherType then appears at bytes 16-17.
		We shift the view by 4 bytes so the rest of the function
		sees a normal Ethernet layout (EtherType at offset 12).	*/

	const int is_vlan_packet = (
		length						>= SAFE_SV_MIN_FRAME + 4U	&&
		ethernet_frame[ETH_ETHERTYPE_OFFSET	]	== VLAN_TPID_HI			&&
		ethernet_frame[ETH_ETHERTYPE_OFFSET + 1U]	== VLAN_TPID_LO
	);

	const	u8	*const	frame		= is_vlan_packet ? (ethernet_frame	+ 4U)	: ethernet_frame;
	const	u32		frame_length	= is_vlan_packet ? (length		- 4U)	: length;

	/*@ assert
			frame_length >= SAFE_SV_MIN_FRAME &&
			frame_length <= SAFE_SV_MAX_FRAME;
	*/

	if (
		frame[ETH_ETHERTYPE_OFFSET	] != SV_ETHERTYPE_HI ||
		frame[ETH_ETHERTYPE_OFFSET + 1U	] != SV_ETHERTYPE_LO
	) {
		return_filter (SV_REJECT_ETH_TYPE,ETH_ETHERTYPE_OFFSET);
	}

	if (frame_length < ETH_HEADER_LENGTH + 2U) {
		return_filter (SV_REJECT_SIZE,ETH_HEADER_LENGTH);
	}

	/* APPID: IEC 61850-9-2 assigns 0x4000-0x7FFF for SV */

	const u32 appid = (	(u32)frame[ETH_HEADER_LENGTH		] * 256U) +
				(u32)frame[ETH_HEADER_LENGTH + 1U	];

	if (appid < SV_APPID_MIN || appid > SV_APPID_MAX) {
		return_filter (SV_REJECT_APPID,ETH_HEADER_LENGTH);
	}

	const u32 sv_len = (
		((u32)frame[PROTOCOL_HEADER_LENGTH_OFFSET	] << 8) |
		(u32) frame[PROTOCOL_HEADER_LENGTH_OFFSET + 1U	]
	);

	const U32 sv_frame_end = ADD(ETH_HEADER_LENGTH, sv_len);

	if (sv_frame_end.overflowed || sv_frame_end.value > frame_length) {
		return_filter (SV_REJECT_HEADER_LENGTH,PROTOCOL_HEADER_LENGTH_OFFSET);
	}

	u32 offset = APDU_OFFSET;

	if (offset >= frame_length || frame[offset] != SV_OUTER_TAG) {
		return_filter (SV_REJECT_OUTER_TAG,offset);
	}

#ifndef SAFE_IGNORE_RESERVED_SV
	/* Reserved1/Reserved2 validation (IEC 61850-9-2 Fig 3). The outer-tag check
	 * above established frame_length > APDU_OFFSET (22), so RESERVED1/RESERVED2
	 * (offsets 18-21) are within the frame. All Reserved-field checks below
	 * are skipped when SAFE_IGNORE_RESERVED_SV is defined (e.g. IEC 62351-6
	 * secured SV, which populates the Reserved Security field). */

	/* Reserved1 bit 0: S (simulated). Operational filter rejects simulated frames. */
	if ((frame[RESERVED1_OFFSET] & SIM_BIT_MASK) == SIM_BIT_MASK) {
		return_filter (SV_REJECT_SIM,RESERVED1_OFFSET);
	}

	/* Reserved1 bits 1-3: R, shall be 0 (IEC 61850-9-2). */
	if ((frame[RESERVED1_OFFSET] & RESERVED_R_MASK) != 0x00U) {
		return_filter (SV_REJECT_RESERVED,RESERVED1_OFFSET);
	}

	/* Reserved Security field (Reserved1 bits 4-15 + Reserved2): shall be 0 for
	 * unsecured SV (IEC 62351-6 populates it when security is used). */
	if (
		(frame[RESERVED1_OFFSET		] & RESERVED_SEC_MASK)	!= 0x00U ||
		 frame[RESERVED1_OFFSET + 1U	]			!= 0x00U ||
		 frame[RESERVED2_OFFSET		]			!= 0x00U ||
		 frame[RESERVED2_OFFSET + 1U	]			!= 0x00U
	) {
		return_filter (SV_REJECT_RESERVED,RESERVED1_OFFSET);
	}
#endif

	++offset;

	/*@
		assert
			offset <= frame_length;
	*/

	/*@
		assert
			\separated(&offset, frame + (0 .. frame_length - 1));
	*/

	const U32 pdu_len_R = read_length(frame, frame_length, &offset);
	if (pdu_len_R.overflowed) {
		return_filter (SV_REJECT_TRUNCATE,offset);
	}
	const u32 pdu_len = pdu_len_R.value;

	/*@ assert offset <= frame_length; */

	const U32 sv_pdu_sum = ADD(offset, pdu_len);

	if (sv_pdu_sum.overflowed || sv_pdu_sum.value > frame_length) {
		return_filter (SV_REJECT_TRUNCATE,offset);
	}

	const	u32 pdu_end		= sv_pdu_sum.value;
		u32 declared_asdu_count	= 0U;

	/*@
		loop invariant
				offset <= frame_length;

		loop invariant
				pdu_end <= frame_length;

		loop invariant
				out.asdu_count <= SAFE_SV_MAX_ASDU;

		loop assigns
				offset,
				declared_asdu_count,
				out;

		loop variant
				pdu_end - offset;
	*/
	while (offset < pdu_end)
	{
		if (offset >= frame_length) {
			return_filter (SV_REJECT_TRUNCATE,offset);
		}

		/*@ assert
			offset < frame_length;
		*/

		const u8 tag = frame[offset++];

		/*@ assert
			offset <= frame_length;
		*/

		/*@ assert
			\separated(&offset, frame + (0 .. frame_length - 1));
		*/

		const U32 tlv_len_R = read_length(frame, frame_length, &offset);
		if (tlv_len_R.overflowed) {
			return_filter (SV_REJECT_TRUNCATE,offset);
		}
		const u32 tlv_len = tlv_len_R.value;

		/*@ assert offset <= frame_length; */

		const U32 tlv_end = ADD(offset, tlv_len);

		if (tlv_end.overflowed || tlv_end.value > frame_length) {
			return_filter (SV_REJECT_TRUNCATE,offset);
		}

		if (tag == SV_NOASDU_TAG)
		{
			/* noASDU: read declared ASDU count */

			if (tlv_len == 1U && offset < frame_length) {
				declared_asdu_count = (u32)frame[offset];
			}
		}
		else if (tag == SV_SEQASDU_TAG)
		{
			/* seqASDU - iterate ASDUs */

				u32 asdu_offset	= offset;
			const	u32 asdu_end	= tlv_end.value;

			/*@
				loop invariant
						asdu_offset <= frame_length;

				loop invariant
						asdu_end <= frame_length;

				loop invariant
						out.asdu_count <= SAFE_SV_MAX_ASDU;

				loop assigns
						asdu_offset,
						out;

				loop variant
						asdu_end - asdu_offset;
			*/
			while (asdu_offset < asdu_end)
			{
				if (out.asdu_count >= SAFE_SV_MAX_ASDU) {
					return_filter (SV_REJECT_ASDU_COUNT,asdu_offset);
				}

				if (
					asdu_offset		>= frame_length	||
					frame[asdu_offset]	!= SV_ASDU_SEQ_TAG
				) {
					return_filter (SV_REJECT_ASDU_TAG,asdu_offset);
				}

				const U32 inner_start = ADD(asdu_offset, 1U);

				if (inner_start.overflowed || inner_start.value > frame_length) {
					return_filter (SV_REJECT_TRUNCATE,asdu_offset);
				}

				u32 inner_offset = inner_start.value;

				/*@ assert
					inner_offset <= frame_length;
				*/

				/*@ assert
					\separated(&inner_offset, frame + (0 .. frame_length - 1));
				*/

				const U32 asdu_len_R = read_length (
								frame,
								frame_length,
								&inner_offset
				);
				if (asdu_len_R.overflowed) {
					return_filter (SV_REJECT_TRUNCATE,inner_offset);
				}
				const u32 asdu_len = asdu_len_R.value;

				/*@ assert
					inner_offset <= frame_length;
				*/

				const U32 asdu_end_off = ADD(inner_offset, asdu_len);

				if (asdu_end_off.overflowed || asdu_end_off.value > frame_length) {
					return_filter (SV_REJECT_TRUNCATE,inner_offset);
				}

					u32 validation_offset = 0U;

				const	u32 validation_result = sv_validate_asdu (
									frame + inner_offset,
									asdu_len,
									&validation_offset
				);

				if (validation_result != 0U)
				{
					/* validation_offset < asdu_len, inner_offset + asdu_len <= length: no overflow */

					const U32 sv_rej = ADD(inner_offset, validation_offset);

					return_filter (validation_result,sv_rej.overflowed ? inner_offset : sv_rej.value);
				}

				asdu_offset = asdu_end_off.value;

				out.asdu_count++;
			}
		}
		else {
			return_filter (SV_REJECT_FIELD_TAG,PREVIOUS(offset));
		}

		offset = tlv_end.value;
	}

	/* Check 4: no trailing bytes after savPdu */
	if (offset != pdu_end) {
		return_filter (SV_REJECT_TRAILING,offset);
	}

	/* Check 5: at least one ASDU must be present */
	if (out.asdu_count == 0U) {
		return_filter (SV_REJECT_ASDU_COUNT,0U);
	}

	/*
		Check 6: noASDU is mandatory and must equal the actual ASDU count.
		out.asdu_count is already in 1..SAFE_SV_MAX_ASDU (Checks 5 + loop cap),
		so this also rejects noASDU == 0 and a missing/oversized noASDU field.
	*/
	if (declared_asdu_count != out.asdu_count) {
		return_filter (SV_REJECT_NOASDU,0U);
	}

	return out;
}

/* ==========================================================
 * SafeIEC104 - IEC 60870-5-104 APDU whitelist filter
 * ========================================================== */

/*
 * IEC104_ELEMENT_SIZE[TypeID] - bytes per information object element
 * (after the 3-byte IOA). 0xFF = TypeID not permitted.
 *
 * Sources: IEC 60870-5-101 Part 4 companion standard + -104 annex.
 * Monitoring direction (process information in monitor direction):
 *	M_SP_NA_1 (1)  1 byte  - single-point, no time
 *	M_DP_NA_1 (3)  1 byte  - double-point, no time
 *	M_ST_NA_1 (5)  2 bytes - step position, no time
 *	M_BO_NA_1 (7)  5 bytes - bitstring, no time
 *	M_ME_NA_1 (9)  3 bytes - measured NVA, no time
 *	M_ME_NB_1 (11) 3 bytes - measured SVA, no time
 *	M_ME_NC_1 (13) 5 bytes - measured short float, no time
 *	M_IT_NA_1 (15) 5 bytes - integrated totals, no time
 *	M_ME_ND_1 (21) 2 bytes - measured NVA, no quality
 *	M_SP_TB_1 (30) 8 bytes - single-point + CP56Time2a
 *	M_DP_TB_1 (31) 8 bytes - double-point + CP56Time2a
 *	M_ST_TB_1 (32) 9 bytes - step position + CP56Time2a
 *	M_BO_TB_1 (33) 12 bytes - bitstring + CP56Time2a
 *	M_ME_TD_1 (34) 10 bytes - NVA + CP56Time2a
 *	M_ME_TE_1 (35) 10 bytes - SVA + CP56Time2a
 *	M_ME_TF_1 (36) 12 bytes - float + CP56Time2a
 *	M_IT_TB_1 (37) 12 bytes - integrated totals + CP56Time2a
 *	M_EP_TD_1 (38) 10 bytes - event of protection + CP56Time2a
 *	M_EP_TE_1 (39) 11 bytes - packed start events + CP56Time2a
 *	M_EP_TF_1 (40) 11 bytes - packed output circuit + CP56Time2a
 *	M_EI_NA_1 (70) 1 byte  - end of initialisation
 * Command/control direction (behind optional compile guards):
 *	C_SC_NA_1 (45) 1 byte
 *	C_DC_NA_1 (46) 1 byte
 *	C_RC_NA_1 (47) 1 byte
 *	C_SE_NA_1 (48) 3 bytes
 *	C_SE_NB_1 (49) 3 bytes
 *	C_SE_NC_1 (50) 5 bytes
 *	C_BO_NA_1 (51) 4 bytes
 *	C_SC_TA_1 (58) 8 bytes
 *	C_DC_TA_1 (59) 8 bytes
 *	C_RC_TA_1 (60) 8 bytes
 *	C_SE_TA_1 (61) 10 bytes
 *	C_SE_TB_1 (62) 10 bytes
 *	C_SE_TC_1 (63) 12 bytes
 *	C_BO_TA_1 (64) 11 bytes
 *	C_IC_NA_1 (100) 1 byte	- interrogation command
 *	C_CI_NA_1 (101) 1 byte	- counter interrogation
 *	C_RD_NA_1 (102) 0 bytes	- read command (IOA only)
 *	C_CS_NA_1 (103) 7 bytes	- clock synchronisation
 */

/* Single source of truth for the permitted TypeID subset and each TypeID's
 * information-element size. IEC104_ELEMENT_SIZE and IEC104_TYPEID_WHITELIST are both
 * generated from these lists, so the two tables can never drift apart. */
#define IEC104_TYPES_BASE(X)						\
	X(  1,  1)	/* M_SP_NA_1 single-point, no time	*/	\
	X(  3,  1)	/* M_DP_NA_1 double-point, no time	*/	\
	X(  5,  2)	/* M_ST_NA_1 step position		*/	\
	X(  7,  5)	/* M_BO_NA_1 bitstring			*/	\
	X(  9,  3)	/* M_ME_NA_1 meas. NVA			*/	\
	X( 11,  3)	/* M_ME_NB_1 meas. SVA			*/	\
	X( 13,  5)	/* M_ME_NC_1 meas. short float		*/	\
	X( 15,  5)	/* M_IT_NA_1 integrated totals		*/	\
	X( 21,  2)	/* M_ME_ND_1 meas. NVA, no QDS		*/	\
	X( 30,  8)	/* M_SP_TB_1 single-point + time	*/	\
	X( 31,  8)	/* M_DP_TB_1 double-point + time	*/	\
	X( 32,  9)	/* M_ST_TB_1 step position + time	*/	\
	X( 33, 12)	/* M_BO_TB_1 bitstring + time		*/	\
	X( 34, 10)	/* M_ME_TD_1 NVA + time			*/	\
	X( 35, 10)	/* M_ME_TE_1 SVA + time			*/	\
	X( 36, 12)	/* M_ME_TF_1 float + time		*/	\
	X( 37, 12)	/* M_IT_TB_1 integ. totals + time	*/	\
	X( 38, 10)	/* M_EP_TD_1 prot. event + time		*/	\
	X( 39, 11)	/* M_EP_TE_1 packed start evt + time	*/	\
	X( 40, 11)	/* M_EP_TF_1 packed out ckt + time	*/	\
	X( 70,  1)	/* M_EI_NA_1 end of initialisation	*/	\
	X(100,  1)	/* C_IC_NA_1 interrogation command	*/	\
	X(101,  1)	/* C_CI_NA_1 counter interrogation	*/	\
	X(102,  0)	/* C_RD_NA_1 read (IOA only)		*/

#define IEC104_TYPES_COMMANDS(X)					\
	X( 45,  1)	/* C_SC_NA_1 single command		*/	\
	X( 46,  1)	/* C_DC_NA_1 double command		*/	\
	X( 47,  1)	/* C_RC_NA_1 regulating step		*/	\
	X( 48,  3)	/* C_SE_NA_1 setpoint NVA		*/	\
	X( 49,  3)	/* C_SE_NB_1 setpoint SVA		*/	\
	X( 50,  5)	/* C_SE_NC_1 setpoint float		*/	\
	X( 51,  4)	/* C_BO_NA_1 bitstring command		*/	\
	X( 58,  8)	/* C_SC_TA_1 single cmd + time		*/	\
	X( 59,  8)	/* C_DC_TA_1 double cmd + time		*/	\
	X( 60,  8)	/* C_RC_TA_1 step cmd + time		*/	\
	X( 61, 10)	/* C_SE_TA_1 setpoint NVA + time	*/	\
	X( 62, 10)	/* C_SE_TB_1 setpoint SVA + time	*/	\
	X( 63, 12)	/* C_SE_TC_1 setpoint float + time	*/	\
	X( 64, 11)	/* C_BO_TA_1 bitstring cmd + time	*/

#define IEC104_TYPES_CLOCK(X)						\
	X(103,  7)	/* C_CS_NA_1 clock synchronisation	*/

static const u8 IEC104_ELEMENT_SIZE[256] = {
#define X(id, sz)	[id] = (u8)(sz),
	IEC104_TYPES_BASE(X)
#ifdef SAFE_ENABLE_IEC104_COMMANDS
	IEC104_TYPES_COMMANDS(X)
#endif
#ifdef SAFE_ENABLE_IEC104_CLOCK_SYNC
	IEC104_TYPES_CLOCK(X)
#endif
#undef X
};

/* Permitted flag: 1 for every TypeID listed above. Kept as a separate table so
 * the zero default in IEC104_ELEMENT_SIZE (C_RD_NA_1 = 0) is not mistaken for
 * "invalid". Both tables are generated from the same lists (see above). */
static const u8 IEC104_TYPEID_WHITELIST[256] = {
#define X(id, sz)	[id] = 1U,
	IEC104_TYPES_BASE(X)
#ifdef SAFE_ENABLE_IEC104_COMMANDS
	IEC104_TYPES_COMMANDS(X)
#endif
#ifdef SAFE_ENABLE_IEC104_CLOCK_SYNC
	IEC104_TYPES_CLOCK(X)
#endif
#undef X
};

/* U-frame CF1 values that are permitted.
 * Only standard supervisory functions are whitelisted. */
static const u8 IEC104_UFRAME_WHITELIST[256] = {
	[0x07] = 1U,	/* STARTDT act	*/
	[0x0B] = 1U,	/* STARTDT con	*/
	[0x13] = 1U,	/* STOPDT act	*/
	[0x23] = 1U,	/* STOPDT con	*/
	[0x43] = 1U,	/* TESTFR act	*/
	[0x83] = 1U,	/* TESTFR con	*/
};

/* IEC 60870-5-104 APDU constants */
#define IEC104_START_BYTE	0x68U
#define IEC104_APCI_HDR		2U	/* start(1) + length(1)		*/
#define IEC104_CF_LENGTH	4U	/* four control-field bytes	*/
#define IEC104_IOA_LENGTH	3U	/* 3-byte information object address */
#define IEC104_MIN_APDU		6U	/* APCI header only		*/
#define IEC104_MIN_L		4U	/* minimum L (control fields)	*/
#define IEC104_IASDU_MIN_L	10U	/* CF(4) + ASDU_HDR(6)		*/
#define IEC104_VSQ_SQ_BIT	0x80U
#define IEC104_VSQ_N_MASK	0x7FU

/*@
requires // message size bounded to prevent pointer arithmetic overflow
	length <= 65535;

requires // apdu is readable for the given length (or empty)
	length == 0 ||
	\valid_read(apdu + (0 .. length - 1));

assigns
	\nothing;

ensures // under/oversize messages are always rejected
	apdu != \null &&
	(length < IEC104_MIN_APDU || length > SAFE_IEC104_MAX_APDU)
		==> \result.error == IEC104_REJECT_SIZE;

ensures // wrong start byte is always rejected
	apdu != \null &&
	length >= IEC104_MIN_APDU &&
	length <= SAFE_IEC104_MAX_APDU &&
	apdu[0] != IEC104_START_BYTE
		==> \result.error == IEC104_REJECT_START;

ensures // accepted I-frames have at most SAFE_IEC104_MAX_OBJECTS objects
	\result.error == IEC104_OK &&
	\result.frame_type == 0U
		==> \result.object_count <= SAFE_IEC104_MAX_OBJECTS;
*/
SAFE_PURE SafeIec104Result safe_iec104_filter (
	const	u8	*const	apdu,
	const	u32		length
)
{
	SafeIec104Result out = {
				.error		= IEC104_OK,
				.reject_at	= 0U,
				.frame_type	= 0U,
				.typeid		= 0U,
				.object_count	= 0U
	};

	/* Check 1: size bounds */
	if (length < IEC104_MIN_APDU || length > SAFE_IEC104_MAX_APDU) {
		return_filter (IEC104_REJECT_SIZE,0U);
	}

	/* Check 2: start byte */
	if (apdu[0] != IEC104_START_BYTE) {
		return_filter (IEC104_REJECT_START,0U);
	}

	/* Check 3: L field consistency - total frame = 2 + L */
	const u32 L        = apdu[1];
	const U32 claimed  = ADD(IEC104_APCI_HDR, L);

	if (claimed.overflowed || claimed.value > length) {
		return_filter (IEC104_REJECT_LENGTH,1U);
	}

	/* Check 4: L must be at least 4 (four control-field bytes) */
	if (L < IEC104_MIN_L) {
		return_filter (IEC104_REJECT_LENGTH,1U);
	}

	/* Check 5: frame type from CF1 bits [1:0] */
	const u8 cf1 = apdu[2];

	if ((cf1 & 0x01U) == 0x00U)
	{
		/* -------------------------------------------------
		* I-frame: data transfer
		* ------------------------------------------------- */

		out.frame_type = 0U;

		/* I-frames must carry an ASDU: L >= CF(4) + ASDU_HDR(6) */

		if (L < IEC104_IASDU_MIN_L) {
			return_filter (IEC104_REJECT_LENGTH,1U);
		}

		/* ASDU header starts at offset 6 (after APCI + CF) */
		const u32 asdu_off = IEC104_APCI_HDR + IEC104_CF_LENGTH;

		out.typeid = apdu[asdu_off];		/* TypeID	*/

		const u8  variable_structure_qualifier	= apdu[asdu_off + 1U];	/* VSQ byte	*/
		const u8  sequential_bit		= (variable_structure_qualifier & IEC104_VSQ_SQ_BIT) ? 1U : 0U;
		const u32 N				= (u32)(variable_structure_qualifier & IEC104_VSQ_N_MASK);

		/* TypeID whitelist */
		if (! IEC104_TYPEID_WHITELIST[out.typeid]) {
			return_filter (IEC104_REJECT_TYPEID,asdu_off);
		}

		/* N must be at least 1 and within configured maximum */
		if (N == 0U || N > SAFE_IEC104_MAX_OBJECTS) {
			return_filter (IEC104_REJECT_OBJECTS,asdu_off + 1U);
		}

		const u8  element	= IEC104_ELEMENT_SIZE[out.typeid];
		const u32 obj_size	= IEC104_IOA_LENGTH + (u32)element;

		/*
			Check 6: body length must exactly match declared objects.
			body = L - CF(4) - ASDU_HDR(6) = L - 10
		*/
		const U32 body_sub = SUBTRACT(L, IEC104_IASDU_MIN_L);

		if (body_sub.underflowed) {
			return_filter (IEC104_REJECT_TRUNCATE,1U);
		}

		const u32 body_length = body_sub.value;

		u32 expected_body;

		if (sequential_bit == 0U)
		{
			/* SQ=0: N independent objects, each with its own IOA.
			 * Accumulate N * obj_size using ADD to stay overflow-free. */
			u32 byte_total = 0U;

			/*@
				loop invariant 0 <= i <= N;
				loop invariant 0 <= byte_total;
				loop assigns i, byte_total;
				loop variant N - i;
			*/
			for (u32 i = 0U; i < N; i++)
			{
				const U32 step = ADD(byte_total, obj_size);

				if (step.overflowed) {
					return_filter (IEC104_REJECT_TRUNCATE,asdu_off + 1U);
				}

				byte_total = step.value;
			}

			expected_body = byte_total;
		}
		else
		{
			/* SQ=1: single IOA followed by N consecutive elements.
			* element = 0 with SQ = 1 has no defined meaning; reject. */

			if (element == 0U) {
				return_filter (IEC104_REJECT_OBJECTS,asdu_off + 1U);
			}

			/* element --- 255 (u8), N --- 127 (checked above)
			 * -> product --- 32385, no u32 overflow possible. */

			/*@ assert (u32)element	<= 255U;			*/
			/*@ assert N		<= SAFE_IEC104_MAX_OBJECTS;	*/

			const U32 Elements = ADD(IEC104_IOA_LENGTH, (u32)element * N);

			if (Elements.overflowed) {
				return_filter (IEC104_REJECT_TRUNCATE,asdu_off + 1U);
			}

			expected_body = Elements.value;
		}

		if (body_length != expected_body) {
			return_filter (IEC104_REJECT_TRUNCATE,asdu_off);
		}

		out.object_count = N;
	}
	else if (cf1 == 0x01U)
	{
		/* -------------------------------------------------
		* S-frame: acknowledgement only, no ASDU.
		* CF1 is fixed at 0x01 (IEC 60870-5-104); any other
		* "S-like" CF1 falls through to the U-frame whitelist
		* and is rejected.
		* ------------------------------------------------- */

		out.frame_type = 1U;

		if (L != IEC104_CF_LENGTH) {
			return_filter (IEC104_REJECT_LENGTH,1U);
		}
	}
	else
	{
		/* -------------------------------------------------
		* U-frame: unnumbered (STARTDT/STOPDT/TESTFR)
		* ------------------------------------------------- */

		out.frame_type = 2U;

		if (L != IEC104_CF_LENGTH) {
			return_filter (IEC104_REJECT_LENGTH,1U);
		}

		if (! IEC104_UFRAME_WHITELIST[cf1]) {
			return_filter (IEC104_REJECT_UFRAME,2U);
		}
	}

	return out;
}
