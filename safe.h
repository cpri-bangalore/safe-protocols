/*

safe.h - Safe Protocol Subset Filters.

==== Copyright (c) 2026 Central Power Research Institute, Bangalore ====

	Smart Grid Research Laboratory, CPRI
	sgrl [HYPHEN] cpri [AT] cpri [DOT] in

	This version of safe.c/safe.h is not free software; and can
	ONLY be used for evaluation, research, and educational purposes.

========================================================================

Five whitelist filters for IEC 61850 and DNP3.
Each returns a result struct: 0 on accept,
nonzero rejection code with byte offset on reject.

*/

#ifndef SAFE_H
#define SAFE_H

/* Two-level indirection so __LINE__ expands before the ## paste; otherwise
 * every assert would share the literal name "___Error___At___Line_____LINE__". */
#define Compile_Time_Assert_CONCAT_(_a_,_b_)	_a_##_b_
#define Compile_Time_Assert_CONCAT(_a_,_b_)	Compile_Time_Assert_CONCAT_(_a_,_b_)
#define Compile_Time_Assert(_condition_)		\
	extern char Compile_Time_Assert_CONCAT(___Error___At___Line___,__LINE__)[(_condition_) ? 1 : -1];

#define PREVIOUS(_offset_) ((_offset_) > 0 ? ((_offset_) - 1) : 0)

#define return_asn(_error_,_offset_) {			\
	return (SafeAsnResult){ .error = _error_, .reject_at = _offset_ };	\
}

/* Shared rejection/return for the five protocol filters: each declares its
 * result struct as `out`, so one macro serves all of them (GOOSE/SV/MMS/
 * DNP3/IEC104). The ASN walkers use return_asn (compound literal) instead. */
#define return_filter(_error_,_offset_) {		\
	out.error	= _error_;			\
	out.reject_at	= _offset_;			\
							\
	return out;					\
}



/*
=== Fixed integers definitions ===

On most systems, this should just work.
If not, and add a #include<stdint.h>,
and replace in below typedefs:

	"unsigned char"		with "uint8_t"
	"unsigned short"	with "uint16_t"
	"unsigned int"		with "uint32_t"
	"unsigned long long"	with "uint64_t"
	"long long"		with "int64_t"

*/
typedef unsigned char		u8;
typedef unsigned short		u16;
typedef unsigned int		u32;
typedef unsigned long long	u64;
typedef long long		i64;

/* Check if our typedefs are correct */
Compile_Time_Assert(sizeof(u8)	== 1)
Compile_Time_Assert(sizeof(u16)	== 2)
Compile_Time_Assert(sizeof(u32)	== 4)
Compile_Time_Assert(sizeof(u64)	== 8)

#ifndef UINT32_MAX
	#define UINT32_MAX (0xFFFFFFFFU)
#endif

#include "safe_config.h"

typedef struct {

	u8	overflowed;
	u8	underflowed;

	u32	value;

} U32;

/*@
assigns
	\nothing;

ensures // that results dont underflow
	\result.underflowed == 0;

behavior no_overflow:
	assumes (integer)a + (integer)b	<= (integer)UINT32_MAX;
	ensures \result.overflowed	== 0;
	ensures (integer)\result.value	== (integer)a + (integer)b;

behavior overflow:
	assumes (integer)a + (integer)b > (integer)UINT32_MAX;
	ensures \result.overflowed == 1;

complete
	behaviors;
disjoint
	behaviors;

*/
static inline U32 ADD(u32 a, u32 b)
{
	U32 sum = {
		.overflowed	= 0,
		.underflowed	= 0,
		.value		= 0
	};

	/* cast before add: prevents u32 wrap */

	const u64 sum_64 = (u64)a + (u64)b;

	if (sum_64 > (u64)UINT32_MAX)
	{
		sum.overflowed = 1;
		return sum;
	}

	sum.value = (u32)sum_64;

	return sum;
}

/*@
assigns
	\nothing;

ensures // that results dont overflow
	\result.overflowed == 0;

behavior no_underflow:
	assumes a			>= b;
	ensures \result.underflowed	== 0;
	ensures (integer)\result.value	== (integer)a - (integer)b;

behavior underflow:
	assumes a			< b;
	ensures \result.underflowed	== 1;

complete
	behaviors;
disjoint
	behaviors;

*/
static inline U32 SUBTRACT(u32 a, u32 b)
{
	U32 sub = {
		.overflowed	= 0,
		.underflowed	= 0,
		.value		= 0
	};

	if (a < b)
	{
		sub.underflowed = 1;
		return sub;
	}

	sub.value = a - b;	/* safe: a >= b, no u32 wrap */

	return sub;
}

/* -- Internal wire-format constants ------------------------ */

#define ETH_HEADER_LENGTH		14U
#define ETH_ETHERTYPE_OFFSET		12U
#define PROTOCOL_HEADER_LENGTH_OFFSET	16U
#define APDU_OFFSET			22U /*ETH=14 + AppId=2 + Length=2
								+ Reserved=4 */

/* Reserved1/Reserved2 header fields (IEC 61850-8-1 Fig C.5; IEC 61850-9-2
 * Fig 3), relative to the de-VLANned link frame, immediately after the 2-byte
 * protocol Length field. Bit 0 is the MSB of the first octet:
 *   Reserved1 bit 0    = S  (simulated frame)
 *   Reserved1 bits 1-3 = R  (reserved, shall be 0)
 *   Reserved1 bits 4-15 + Reserved2 = Reserved Security (IEC 62351-6; shall be
 *                        0 when GOOSE/SV is transmitted without security). */
#define RESERVED1_OFFSET		18U	/* PROTOCOL_HEADER_LENGTH_OFFSET + 2 */
#define RESERVED2_OFFSET		20U
#define SIM_BIT_MASK			0x80U	/* Reserved1 bit 0: S (simulated)     */
#define RESERVED_R_MASK			0x70U	/* Reserved1 bits 1-3: R (shall be 0) */
#define RESERVED_SEC_MASK		0x0FU	/* Reserved1 bits 4-7: security field */

/* Fixed protocol constants (not configurable)	*/
#define ASN_TAG_BOOLEAN			0x01U
#define ASN_TAG_INTEGER			0x02U
#define ASN_TAG_BITSTRING		0x03U
#define ASN_TAG_OCTET_STRING		0x04U
#define ASN_TAG_NULL			0x05U
#define ASN_TAG_OID			0x06U
#define ASN_TAG_UTF8_STRING		0x0CU

#define ASN_TAG_PRINTABLE_STRING	0x13U
#define ASN_TAG_IA5_STRING		0x16U
#define ASN_TAG_VISIBLE_STRING		0x1AU
#define ASN_TAG_UTCTIME			0x17U
#define ASN_TAG_SEQUENCE		0x30U
#define ASN_TAG_SET			0x31U
#define ASN_TAG_ENUMERATED		0x0AU

#define BER_LONG_FORM_BIT		0x80U
#define BER_LENGTH_MASK			0x7FU
#define BER_HIGH_TAG_MASK		0x1FU
#define BER_INDEFINITE_LENGTH		0x80U
#define BER_CONTINUATION_BIT		0x80U
#define BER_SIGN_BIT			0x80U

#define DNP3_RESPONSE_BIT		0x80U
#define DNP3_FC_CONFIRM			0x00U
#define DNP3_FC_READ			0x01U
#define DNP3_FC_ENABLE_UNSOLICITED	0x14U
#define DNP3_FC_DISABLE_UNSOLICITED	0x15U
#define DNP3_FC_ASSIGN_CLASS		0x16U
#define DNP3_FC_DELAY_MEASURE		0x17U

#define ASN_MAX_LENGTH_BYTES		4U

#define VLAN_TPID_HI			0x81U	/* IEEE 802.1Q TPID high byte */
#define VLAN_TPID_LO			0x00U	/* IEEE 802.1Q TPID low byte,
						   TPID 0x8100 = VLAN tag      */

#define GOOSE_MIN_FRAME			22U
#define GOOSE_OUTER_TAG			0x61U
#define GOOSE_DATA_BOOLEAN_TAG		0x83U	/* allData: boolean		*/
#define GOOSE_DATA_BIT_STRING_TAG	0x84U	/* allData: bit-string		*/
#define GOOSE_DATA_INTEGER_TAG		0x85U	/* allData: integer		*/
#define GOOSE_DATA_UNSIGNED_TAG		0x86U	/* allData: unsigned		*/
#define GOOSE_DATA_FLOAT_TAG		0x87U	/* allData: float32		*/
#define GOOSE_DATA_OCTET_STRING_TAG	0x89U	/* allData: octet-string	*/
#define GOOSE_DATA_VISIBLE_STRING_TAG	0x8AU	/* allData: visible-string	*/
#define GOOSE_DATA_MMS_STRING_TAG	0x90U	/* allData: mms-string		*/
#define GOOSE_DATA_TIMESTAMP_TAG	0x91U	/* allData: utc-time		*/
#define GOOSE_DATA_ARRAY_TAG		0xA1U	/* allData: array		*/
#define GOOSE_DATA_STRUCTURE_TAG	0xA2U	/* allData: structure		*/
#define GOOSE_ETHERTYPE_HI		0x88U	/* IEEE 802.1Q / IEC 61850 */
#define GOOSE_ETHERTYPE_LO		0xB8U	/* EtherType 0x88B8 = GOOSE */

#define SV_OUTER_TAG			0x60U
#define SV_NOASDU_TAG			0x80U
#define SV_SEQASDU_TAG			0xA2U
#define SV_ASDU_SEQ_TAG			0x30U
#define SV_SMPSYNC_TAG			0x85U	/* smpSynch field tag		*/
#define SV_SMPMOD_TAG			0x88U	/* smpMod field tag		*/
#define SV_ETHERTYPE_HI			0x88U	/* IEEE 802.1Q / IEC 61850 */
#define SV_ETHERTYPE_LO			0xBAU	/* EtherType 0x88BA = SV    */
#define SV_APPID_MIN			0x4000U	/* IEC 61850-9-2 SV APPID range */
#define SV_APPID_MAX			0x7FFFU

#define SAFE_SV_MIN_FRAME		22U

#define MMS_PDU_CONFIRMED_REQUEST	0xA0U
#define MMS_PDU_CONFIRMED_RESPONSE	0xA1U
#define MMS_PDU_CONFIRMED_ERROR		0xA2U
#define MMS_PDU_UNCONFIRMED		0xA3U
#define MMS_PDU_REJECT			0xA4U
#define MMS_PDU_CANCEL_REQUEST		0xA5U /* cancelRequestPDU  [5] IMPLICIT InvokeID      */
#define MMS_PDU_CANCEL_RESPONSE		0xA6U /* cancelResponsePDU [6] IMPLICIT InvokeID      */
#define MMS_PDU_CANCEL_ERROR		0xA7U /* cancelErrorPDU    [7] IMPLICIT SEQUENCE {...} */
#define MMS_PDU_INITIATE_REQUEST	0xA8U
#define MMS_PDU_INITIATE_RESPONSE	0xA9U
#define MMS_PDU_INITIATE_ERROR		0xAAU
#define MMS_PDU_CONCLUDE_REQUEST	0x8BU
#define MMS_PDU_CONCLUDE_RESPONSE	0x8CU
#define MMS_PDU_CONCLUDE_ERROR		0xADU

#define MMS_SERVICE_INFORMATION_REPORT	0U

#define SAFE_DNP3_MIN_APP		2U

#define SAFE_MAX_CONTINUATION_BYTES	3U

/* -- Compiler hints ---------------------------------------- */

#if defined(__GNUC__) || defined(__clang__)
	#define SAFE_CONST	__attribute__((const))
#else
	#define SAFE_CONST
#endif

#if defined(SAFE_RUN_BENCHMARKS)
	#define SAFE_PURE
#elif defined(__GNUC__) || defined(__clang__)
	#define SAFE_PURE	__attribute__((pure))
#else
	#define SAFE_PURE
#endif

/* -- SafeASN.1 ------------------------------------------- */

#define ASN_OK				0U
#define ASN_REJECT_TAG			1U
#define ASN_REJECT_LENGTH		2U
#define ASN_REJECT_DEPTH		3U
#define ASN_REJECT_INDEF		4U
#define ASN_REJECT_TRUNCATE		5U
#define ASN_REJECT_BADINT		6U
#define ASN_REJECT_SIZE			7U
#define ASN_REJECT_CONTENT		8U
#define ASN_REJECT_NULL			9U
#define ASN_REJECT_TOO_MANY_NODES	10U
#define ASN_REJECT_SET_MULTI		11U

typedef struct
{
	u32 error;
	u32 reject_at;

} SafeAsnResult;

SAFE_PURE SafeAsnResult safe_asn_filter (
	const	u8	*asn_data,
	const	u32	length
);

SAFE_PURE SafeAsnResult safe_asn_filter_relaxed (
	const	u8	*asn_data,
	const	u32	length
);

/* -- SafeASN.1 Parser (filter + node extraction) --------- */

typedef struct
{
		u8	tag;
		u32	length;
	const	u8	*content;	/* points into asn_data -- valid only while asn_data is alive */
		u32	depth;

} SafeAsnNode;

typedef struct
{
	u32			error;
	u32			reject_at;

	u32			node_count;
	SafeAsnNode		nodes[SAFE_ASN_MAX_NODES];

} SafeAsnParseResult;

u32 safe_asn_parse (
	const	u8		*asn_data,
		u32		length,
	SafeAsnParseResult	*out
);

/* -- SafeGOOSE ------------------------------------------- */

#define GOOSE_OK			0U
#define GOOSE_REJECT_SIZE		1U
#define GOOSE_REJECT_ETH_TYPE		2U
#define GOOSE_REJECT_HEADER_LENGTH	3U
#define GOOSE_REJECT_OUTER_TAG		4U
#define GOOSE_REJECT_FIELD_TAG		5U
#define GOOSE_REJECT_FIELD_SIZE		6U
#define GOOSE_REJECT_TRUNCATE		7U
#define GOOSE_REJECT_DATA_VALUE_TAG	8U
#define GOOSE_REJECT_DATA_VALUE_COUNT	9U
#define GOOSE_REJECT_DATA_VALUE_PADDING	10U
#define GOOSE_REJECT_TEST		11U
#define GOOSE_REJECT_DATA_VALUE_LENGTH	12U	/* integer/unsigned width outside valid range (Table A.2/A.3) */
#define GOOSE_REJECT_FIELD_VALUE	13U	/* Unsigned32 header field value outside [0, 2^32-1] */
#define GOOSE_REJECT_DATA_VALUE_RANGE	14U	/* allData unsigned value outside [0, 2^32-1] */
#define GOOSE_REJECT_SIM		15U	/* Reserved1 S bit set (simulated frame) */
#define GOOSE_REJECT_RESERVED		16U	/* Reserved1/Reserved2 R or security bits nonzero */

typedef struct
{
	u32 error;
	u32 reject_at;

	u32 field;
	u32 data_value_count;

} SafeGooseResult;

SAFE_PURE SafeGooseResult safe_goose_filter (
	const	u8	*ethernet_frame,
	const	u32	 length
);

/* -- SafeSV ---------------------------------------------- */

#define SV_OK			0U
#define SV_REJECT_SIZE		1U
#define SV_REJECT_ETH_TYPE	2U
#define SV_REJECT_HEADER_LENGTH	3U
#define SV_REJECT_OUTER_TAG	4U
#define SV_REJECT_TRUNCATE	5U
#define SV_REJECT_FIELD_TAG	6U
#define SV_REJECT_FIELD_SIZE	7U
#define SV_REJECT_ASDU_TAG	8U
#define SV_REJECT_ASDU_COUNT	9U
#define SV_REJECT_APPID		10U
#define SV_REJECT_CONTENT	11U
#define SV_REJECT_NOASDU	12U
#define SV_REJECT_TRAILING	13U
#define SV_REJECT_SIM		14U	/* Reserved1 S bit set (simulated frame) */
#define SV_REJECT_RESERVED	15U	/* Reserved1/Reserved2 R or security bits nonzero */

typedef struct
{
	u32 error;
	u32 reject_at;

	u32 asdu_count;

} SafeSvResult;

SAFE_PURE SafeSvResult safe_sv_filter (
	const	u8	*ethernet_frame,
	const	u32	 length
);

/* -- SafeMMS --------------------------------------------- */

#define MMS_OK			0U
#define MMS_REJECT_SIZE		1U
#define MMS_REJECT_PDU_TAG	2U
#define MMS_REJECT_TRUNCATE	3U
#define MMS_REJECT_INNER_SEQ	4U
#define MMS_REJECT_INVOKE_ID	5U
#define MMS_REJECT_SERVICE	6U
#define MMS_REJECT_BODY		7U	/* SafeASN.1 rejected service body content */
#define MMS_REJECT_DER		8U	/* ASN.1 structural (DER) check failed */

typedef struct
{
	u32 error;
	u32 reject_at;

	u32 service_tag;

} SafeMmsResult;

SAFE_PURE SafeMmsResult safe_mms_filter (
	const	u8	*mms_pdu,
	const	u32	length
);

/* -- SafeIEC104 ------------------------------------------ */

#define IEC104_OK			0U
#define IEC104_REJECT_SIZE		1U
#define IEC104_REJECT_START		2U
#define IEC104_REJECT_LENGTH		3U
#define IEC104_REJECT_UFRAME		4U
#define IEC104_REJECT_TYPEID		5U
#define IEC104_REJECT_OBJECTS		6U
#define IEC104_REJECT_TRUNCATE		7U

typedef struct
{
	u32	error;
	u32	reject_at;

	u8	frame_type;	/* 0=I-frame, 1=S-frame, 2=U-frame */
	u8	typeid;
	u32	object_count;

} SafeIec104Result;

SAFE_PURE SafeIec104Result safe_iec104_filter (
	const	u8	*apdu,
	const	u32	length
);

/* -- SafeDNP3 -------------------------------------------- */

#define DNP3_OK				0U
#define DNP3_REJECT_SIZE		1U
#define DNP3_REJECT_FUNCTION_CODE	2U
#define DNP3_REJECT_GROUP		3U
#define DNP3_REJECT_VARIATION		4U
#define DNP3_REJECT_QUALIFIER		5U
#define DNP3_REJECT_OBJ_COUNT		6U
#define DNP3_REJECT_TRUNCATE		7U

typedef struct
{
	u32	error;
	u32	reject_at;

	u8	function_code;
	u32	object_count;

} SafeDnp3Result;

SAFE_PURE SafeDnp3Result safe_dnp3_filter (
	const	u8	*apdu,
	const	u32	length
);

#endif /* SAFE_H */
