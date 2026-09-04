/*
 * safe_config.h
 * =============
 * Deployment configuration for safe protocol filters.
 *
 * WARNING: Changing values in this file may cause the filters
 * to accept messages outside the safe protocol subsets
 * (SafeASN.1, SafeGOOSE, SafeSV, SafeMMS, SafeDNP3).
 *
 * Re-run Frama-C/WP and the test suite after any modification.
 *
 * By default, all risky or rarely-used services are DISABLED.
 * To enable a service, uncomment the corresponding #define
 * before including safe.h.
 */

#ifndef SAFE_CONFIG_H
#define SAFE_CONFIG_H

/* ===========================================================	*/
/* SafeMMS: Optional services (disabled by default)		*/
/* ===========================================================	*/

/* DeleteNamedVariableList [13]: delete data sets from the IED.
 * Risk: attacker can destroy configured data sets used for protection/monitoring.
 * Scenario: commissioning tools use this to clean up temporary data sets.
 * Not a normal operation. */
/* #define SAFE_ENABLE_MMS_DELETE_NVL */

/* FileRename [75] and FileDelete [76]: unconditionally removed from SafeMMS.
 * These file-manipulation services have no compile-time toggle: safe.c drops
 * service codes [75] and [76] from MMS_SERVICE_WHITELIST regardless of
 * configuration, so an attacker can never rename or delete files
 * (config, disturbance records, logs) on the IED filesystem. */

/* Identify [2]: query MMS implementation identity.
 * Risk: information disclosure (vendor, model, firmware version).
 * Scenario: commissioning tools and IED management systems use this to
 * inventory connected devices. Not used during normal operation. */
/* #define SAFE_ENABLE_MMS_IDENTIFY */

/* Status [0]: query MMS server status.
 * Risk: low; discloses operational state.
 * Scenario: some SCADA masters poll Status on reconnection to verify the IED
 * is ready before resuming polling. InformationReport covers health monitoring
 * during normal operation; enable only if the SCADA master requires it on startup. */
/* #define SAFE_ENABLE_MMS_STATUS */

/* Cancel PDUs (0xA5 cancelRequest, 0xA6 cancelResponse, 0xA7 cancelError).
 * Risk: medium; allows cancel-injection attack -- an adversary on the IT side
 * can forge a cancelRequest with a valid InvokeID to abort an in-flight MMS
 * request on the OT side (session-layer denial of service).
 * Scenario: enable only if the SCADA master or IED requires MMS cancellation
 * (rare; most IEC 61850 implementations do not implement this feature). */
/* #define SAFE_ENABLE_MMS_CANCEL */

/* ===========================================================	*/
/* SafeGOOSE: Optional services (disabled by default)		*/
/* ===========================================================	*/

/* test=TRUE GOOSE frames are always rejected (GOOSE_REJECT_TEST).
 * Protection relays must ignore test=TRUE GOOSE per IEC 61850-8-1;
 * this is not configurable.  A commissioning tool that needs to
 * process test frames should not use an operational safety filter. */

/* mMSString [16] (UTF8String): IEC 61850-8-1 extension type for allData.
 * Not required for protection relay operation (trip commands use boolean,
 * integer, bit-string, float, timestamp).
 * Enable only if IEDs in the deployment are known to send mMSString values. */
/* #define SAFE_ENABLE_GOOSE_MMS_STRING */

/* ===========================================================	*/
/* SafeDNP3: Optional function codes (disabled by default)	*/
/* ===========================================================	*/

/* Direct Operate (FC 0x05): single-phase control without Select phase.
 * Risk: no confirmation step; accidental/adversarial actuation possible.
 * Scenario: some SCADA systems use DO for non-critical fast-response controls
 * (capacitor bank switching, voltage regulator taps, load shedding) during
 * normal operation. Enable if outstation firmware or SCADA requires it;
 * prefer Select-Before-Operate (FC 0x03+0x04) for protection-related actuations. */
/* #define SAFE_ENABLE_DNP3_DIRECT_OPERATE */

/* Direct Operate No-Ack (FC 0x06): control with no response expected.
 * Risk: same as Direct Operate, plus no error feedback.
 * Scenario: broadcast/multicast trip schemes; rarely used in practice.
 * Only enable if SAFE_ENABLE_DNP3_DIRECT_OPERATE is also set. */
/* #define SAFE_ENABLE_DNP3_DIRECT_OPERATE_NR */

/* Counter Freeze (FC 0x07-0x0C): freeze/clear counters.
 * Risk: can hide historical data or disrupt metering records.
 * Scenario: revenue metering systems freeze counters at billing intervals;
 * this is a legitimate normal operational activity in metering deployments.
 * Enable if the DNP3 outstation is used for energy metering (kWh, demand). */
/* #define SAFE_ENABLE_DNP3_COUNTER_FREEZE */

/* Cold Restart (FC 0x0D): full system reboot.
 * Risk: denial of service.
 * Scenario: maintenance and emergency recovery only; not a normal operation.
 * Mitigation: use physical access or out-of-band management for restarts. */
/* #define SAFE_ENABLE_DNP3_COLD_RESTART */

/* Warm Restart (FC 0x0E): partial restart.
 * Risk: denial of service.
 * Scenario: same as Cold Restart; maintenance/emergency only. */
/* #define SAFE_ENABLE_DNP3_WARM_RESTART */

/* Disable Unsolicited (FC 0x15): silence spontaneous event reports from the outstation.
 * Risk: attacker can suppress alarm and status reporting during an incident.
 * Scenario: some DNP3 masters send Disable Unsolicited on link recovery before
 * re-enabling, as part of the unsolicited startup sequence (IEEE 1815 procedure).
 * This is a normal scenario on reconnection; enable if the master firmware
 * requires it. Unsolicited reporting configuration itself is commissioning-phase. */
/* #define SAFE_ENABLE_DNP3_DISABLE_UNSOLICITED */

/* Assign Class (FC 0x16): reassign data points to different event classes.
 * Risk: attacker can demote critical alarm points to a lower-priority class,
 * reducing their poll frequency or hiding them from the master.
 * Scenario: commissioning-phase operation only; class assignments are fixed
 * at engineering time and should not change during normal operation. */
/* #define SAFE_ENABLE_DNP3_ASSIGN_CLASS */

/* File Transfer (FC 0x19-0x1E, Group 70): DNP3 file services.
 * Risk: firmware injection, unauthorized file access.
 * Normal operation use: disturbance record (COMTRADE/event log) retrieval
 * after fault events is a legitimate operational activity in some deployments.
 * Mitigation: use a separate channel (SSH/SCP/SFTP) for file transfer;
 * enable only if DNP3 file transfer is the sole retrieval path. */
/* #define SAFE_ENABLE_DNP3_FILE_TRANSFER */

/* Secure Authentication (Groups 120-122): DNP3-SA objects.
 * Risk: expands parser attack surface for the authentication sub-protocol.
 * Scenario: legacy deployments without TLS infrastructure may rely on DNP3-SA
 * as the sole authentication mechanism during normal operation; this is
 * a legitimate use case in older SCADA installations.
 * Mitigation: prefer TLS transport (IEEE 1815-2012 and later); enable DNP3-SA
 * only if TLS is not available at the transport layer.
 * NOTE: SA object-body validation is not implemented. Groups 120-122 have no
 * entries in DNP3_POINT_SIZE, so even with this macro defined those objects are
 * rejected (DNP3_REJECT_GROUP, fail-closed). The macro only adds them to the
 * group whitelist; it is reserved for a future SA object grammar and currently
 * admits no SA object. */
/* #define SAFE_ENABLE_DNP3_SECURE_AUTH */

/* Reserved1/Reserved2 header validation for GOOSE and SV (IEC 61850-8-1 Fig C.5;
 * IEC 61850-9-2 Fig 3). By default the filter validates the entire Reserved
 * field: the S (simulated) bit is rejected (GOOSE_REJECT_SIM / SV_REJECT_SIM),
 * and the R bits and the 28-bit Reserved Security field must be 0
 * (GOOSE_REJECT_RESERVED / SV_REJECT_RESERVED).
 * Define SAFE_IGNORE_RESERVED_GOOSE / _SV to skip ALL Reserved-field checks for
 * that protocol. Enable only when a deployment legitimately populates these
 * bytes, e.g. IEC 62351-6 secured GOOSE/SV (nonzero Reserved Security field), or
 * to tolerate a known non-conformant publisher.
 * NOTE: this also disables the simulated-frame (S bit) rejection for that
 * protocol; a site running simulation must use monitor mode, not this flag. */
/* #define SAFE_IGNORE_RESERVED_GOOSE */
/* #define SAFE_IGNORE_RESERVED_SV */

/* ===========================================================	*/
/* Schema bounds (override to tighten or relax per deployment)	*/
/* ===========================================================	*/

/* Maximum number of members allowed in a SET (0x31) by safe_asn_filter_relaxed.
 * X.509 RDN sets are usually single-member, but multi-valued RDNs (RFC 5280) and
 * multi-valued directory attributes / SET OF values (LDAP, e.g. a 2-value
 * objectClass) are legal and common; the relaxed profile admits up to this bound
 * and rejects larger sets (ASN_REJECT_SET_MULTI). */
#ifndef SAFE_MAX_SET_MEMBERS
  #define SAFE_MAX_SET_MEMBERS		(16U)
#endif

/* ASN.1 maximum nesting depth for protocol headers and standalone usage.
 * GOOSE data depth is governed separately by SAFE_GOOSE_MAX_DATA_DEPTH. */
#ifndef SAFE_ASN_MAX_DEPTH
  #define SAFE_ASN_MAX_DEPTH		(8U)
#endif

/* ASN.1 maximum nesting depth for safe_asn_filter_relaxed.
 * CMS/PKCS#7 SignedData reaches depth 10; Kerberos with PA-DATA reaches 9.
 * Empirically measured: max observed = 10 (CMS attached RSA-2048).
 * 16 = 10 (max observed) + 6 (headroom). */
#ifndef SAFE_ASN_RELAXED_MAX_DEPTH
  #define SAFE_ASN_RELAXED_MAX_DEPTH	(16U)
#endif

/* ASN.1 maximum nesting depth for MMS service bodies.
 * MMS InformationReport and ReadResponse carry nested Data structures
 * (Data { structure { Data { ... } } }) that legitimately exceed depth 8.
 * Empirically measured from real ABB/Siemens substation IED captures
 * (ICS-Pcaps Substation dataset, 4863 MMS PDUs): max observed depth = 28.
 * 32 = 28 (max observed) + 4 (headroom for protocol evolution / unseen IEDs).
 * Used by asn_filter_top(), called only from safe_mms_filter(). */
#ifndef SAFE_ASN_MMS_BODY_MAX_DEPTH
  #define SAFE_ASN_MMS_BODY_MAX_DEPTH	(32U)
#endif

/* ASN.1 maximum TLV node count (safe_asn_parse output array size).
 * Empirically measured from real IED captures: maximum observed = 318
 * (getVarAccessAttr TypeDescription from a Siemens IED).
 * 512 = 318 (max observed) + 194 (headroom for protocol evolution). */
#ifndef SAFE_ASN_MAX_NODES
  #define SAFE_ASN_MAX_NODES		(512U)	/* 318 observed in real IED TypeDescription */
#endif

/* Node cap for the relaxed/non-IEC profile (asn_filter_recursive_relaxed), which
 * also validates X.509 / CRL / CMS / PKI objects. The relaxed filter only COUNTS
 * nodes (no storage array, unlike safe_asn_parse), so its only real bound is the
 * 64 KB input buffer: at >= 2 bytes per TLV, at most 32767 nodes can occur. PKI
 * objects (e.g. a multi-hundred-entry CRL) routinely exceed the IEC-sized 512 cap,
 * so the relaxed path uses the byte-length-derived bound instead. */
#ifndef SAFE_ASN_RELAXED_MAX_NODES
  #define SAFE_ASN_RELAXED_MAX_NODES	(32768U)
#endif



/* ASN.1 maximum IA5String length (bytes).
 * IEC 61850 visible strings (gocbRef, datSet, goID) have a
 * maximum of 129 bytes per IEC 61850-8-1 ObjectReference. */
#ifndef SAFE_ASN_MAX_IA5_STRING
  #define SAFE_ASN_MAX_IA5_STRING	(129U)
#endif

/* ASN.1 maximum UTF8String length (bytes).
 * MMS mMSString [16] data value (ISO 9506-2); IEC 61850 Unicode string
 * (Unicode255) is bounded to 255 octets. */
#ifndef SAFE_ASN_MAX_UTF8_STRING
  #define SAFE_ASN_MAX_UTF8_STRING	(255U)
#endif

/* ASN.1 maximum PrintableString length (bytes).
 * X.509 CN/O/C fields; 64 bytes covers RFC 5280 limits. */
#ifndef SAFE_ASN_MAX_PRINTABLE_STRING
	#define SAFE_ASN_MAX_PRINTABLE_STRING	(64U)
#endif

/* ASN.1 VisibleString (0x1A): used in MMS for filenames and object references
 * (ISO 9506-2). Allowed by default; disable if MMS file services are not used. */
#define SAFE_ENABLE_ASN_VISIBLE_STRING

/* ASN.1 maximum VisibleString length (bytes).
 * IEC 61850-8-1 bounds all MMS service strings (RptID, DataSetReference,
 * ObjectReference, GoCBRef) at SIZE(1..129).  MMS filenames under
 * IEC 61850-6 are max 32 chars.  129 is the widest field in the spec. */
#ifndef SAFE_ASN_MAX_VISIBLE_STRING
	#define SAFE_ASN_MAX_VISIBLE_STRING	(129U)
#endif

/* ASN.1 maximum BIT STRING length (bytes).
 * IEC 61850 bit strings (quality flags, optFields) are 1-4 bytes.
 * Default 128 provides headroom for X.509 key usage extensions. */
#ifndef SAFE_ASN_MAX_BIT_STRING
	#define SAFE_ASN_MAX_BIT_STRING		(128U)
#endif

/* ASN.1 maximum OCTET STRING length (bytes).
 * IEC 61850 octet strings: EntryID (8 bytes), IP (4/16 bytes), MAC (6 bytes).
 * Default 128 provides headroom for certificate identifiers. */
#ifndef SAFE_ASN_MAX_OCTET_STRING
	#define SAFE_ASN_MAX_OCTET_STRING	(128U)
#endif

/* ASN.1 maximum OBJECT IDENTIFIER content length (bytes).
 * MMS/ACSE OIDs (application-context-name, abstract/transfer syntax) are short;
 * 16 bytes covers all practical IEC 61850 MMS object identifiers. */
#ifndef SAFE_ASN_MAX_OID
	#define SAFE_ASN_MAX_OID		(16U)
#endif

/* ASN.1 maximum message size (bytes).
 * DER 2-byte definite length / TPKT limit. */
#ifndef SAFE_ASN_MAX_MESSAGE
	#define SAFE_ASN_MAX_MESSAGE		(65535U)
#endif

/* GOOSE maximum APDU size (bytes).
 * GOOSE is Ethernet-layer (no IP reassembly); APDU begins at byte 22
 * (14 B ETH + 2 B APPID + 2 B Length + 4 B Reserved).
 * 1400 B = 1500 B Ethernet payload - 8 B IEC header - headroom for
 * 802.1Q / Q-in-Q VLAN tags; matches the IEC 61850-8-1 APDU limit. */
#ifndef SAFE_GOOSE_MAX_APDU
	#define SAFE_GOOSE_MAX_APDU		(1400U)
#endif

/* GOOSE maximum data values per allData.
 * Production SCL files use < 40. Default 64 provides headroom. */
#ifndef SAFE_GOOSE_MAX_DATA_VALUES
	#define SAFE_GOOSE_MAX_DATA_VALUES	(64U)
#endif

/* GOOSE maximum nesting depth for allData arrays and structures.
 * IEC 61850-8-1 data models nest at most 2 levels deep in practice.
 * Default 4 provides generous headroom while bounding stack use. */
#ifndef SAFE_GOOSE_MAX_DATA_DEPTH
	#define SAFE_GOOSE_MAX_DATA_DEPTH	(4U)
#endif

/* GOOSE allData per-type content bounds (IEC 61850-8-1 Table A.2/A.3).
 * Used by goose_validate_alldata() for each data-value CHOICE type. */

/* Protocol-fixed content widths -- set by IEC 61850-8-1, do NOT change:
 * boolean = 1 octet; float = 1 format octet + 4 IEEE-754 = 5 octets;
 * utc-time (TimeStamp) = 8 octets; bit-string unused-bits count is 0..7. */
#define SAFE_GOOSE_BOOLEAN_LENGTH			(1U)
#define SAFE_GOOSE_FLOAT_LENGTH			(5U)
#define SAFE_GOOSE_TIMESTAMP_LENGTH		(8U)
#define SAFE_GOOSE_BITSTRING_MAX_UNUSED_BITS	(7U)

/* Tunable per-type size caps (Table A.2 covers all CDC instances;
 * tighten per deployment, never loosen beyond the standard). */
#ifndef SAFE_GOOSE_MAX_OCTET_STRING
	#define SAFE_GOOSE_MAX_OCTET_STRING	(20U)
#endif
#ifndef SAFE_GOOSE_MAX_VISIBLE_STRING
	#define SAFE_GOOSE_MAX_VISIBLE_STRING	(35U)
#endif
#ifndef SAFE_GOOSE_MAX_MMS_STRING
	#define SAFE_GOOSE_MAX_MMS_STRING	(65U)
#endif
#ifndef SAFE_GOOSE_MAX_INTEGER_LENGTH
	#define SAFE_GOOSE_MAX_INTEGER_LENGTH	(9U)	/* INT8..INT64, BER minimal (Table A.3) */
#endif
#ifndef SAFE_GOOSE_MAX_UNSIGNED_LENGTH
	#define SAFE_GOOSE_MAX_UNSIGNED_LENGTH	(5U)	/* INT32U + leading zero byte */
#endif
#ifndef SAFE_GOOSE_MAX_BIT_STRING
	#define SAFE_GOOSE_MAX_BIT_STRING	(128U)	/* 1 unused-bits byte + 127 data bytes */
#endif

/* SV maximum ASDUs per frame.
 * IEC 61850-9-2LE uses 1-2. Default 8 provides 4x headroom. */
#ifndef SAFE_SV_MAX_ASDU
	#define SAFE_SV_MAX_ASDU		(8U)
#endif

/* SV maximum frame size (bytes).
 * SV is an Ethernet-layer protocol (no IP reassembly), so one frame is
 * all you get.  1600 B covers standard Ethernet (1500 B payload) plus
 * 802.1Q / Q-in-Q VLAN overhead and rounds up to a clean boundary.
 * The schema-theoretic limit (8 ASDUs x 525 B = 4200 B) would require
 * jumbo frames, which IEC 61850-9-2LE deployments do not use. */
#ifndef SAFE_SV_MAX_FRAME
	#define SAFE_SV_MAX_FRAME		(1600U)
#endif

/* MMS maximum PDU size (bytes).
 * TPKT 16-bit length field. */
#ifndef SAFE_MMS_MAX_PDU
	#define SAFE_MMS_MAX_PDU		(65535U)
#endif

/* DNP3 maximum application-layer fragment (bytes).
 * IEEE 1815 standard. */
#ifndef SAFE_DNP3_MAX_APP
	#define SAFE_DNP3_MAX_APP		(2048U)
#endif

/* DNP3 maximum request application fragment (bytes).
 * Request PDUs carry only command/qualifier overhead; no bulk data payloads.
 * 256 bytes covers class polls, SBO sequences, and all standard request types. */
#ifndef SAFE_DNP3_MAX_REQUEST_APP
	#define SAFE_DNP3_MAX_REQUEST_APP	(256U)
#endif

/* DNP3 maximum object headers per request fragment.
 * Requests specify 1-4 class objects or a single control object.
 * Default 8 provides generous headroom for multi-class polls. */
#ifndef SAFE_DNP3_MAX_REQUEST_OBJECTS
	#define SAFE_DNP3_MAX_REQUEST_OBJECTS	(8U)
#endif

/* DNP3 maximum object headers per fragment.
 * Production polls use < 10. Default 64 provides 6x headroom. */
#ifndef SAFE_DNP3_MAX_OBJECTS
	#define SAFE_DNP3_MAX_OBJECTS		(64U)
#endif

/* ---------------------------------------------------------------
 * IEC 60870-5-104 configuration
 * --------------------------------------------------------------- */

/* SAFE_ENABLE_IEC104_COMMANDS — enable command TypeIDs (C_SC/DC/RC/SE/BO:
 * 45-51, 58-64).  Disabled by default: commands are write operations;
 * monitor-only deployments should leave this unset. */

/* SAFE_ENABLE_IEC104_CLOCK_SYNC — enable C_CS_NA_1(103) clock
 * synchronisation.  Disabled by default. */

/* IEC 60870-5-104 maximum total APDU size (bytes, including the
 * 2-byte APCI header start+length).  The standard caps the ASDU
 * payload at 249 bytes (L ≤ 253), so the hard maximum is 255.
 * The default matches the standard maximum. */
#ifndef SAFE_IEC104_MAX_APDU
	#define SAFE_IEC104_MAX_APDU		(255U)
#endif

/* IEC 60870-5-104 maximum number of information objects per ASDU.
 * VSQ NSQ field is 7 bits (max 127).  Default is the hard maximum. */
#ifndef SAFE_IEC104_MAX_OBJECTS
	#define SAFE_IEC104_MAX_OBJECTS	(127U)
#endif

#endif /* SAFE_CONFIG_H */
