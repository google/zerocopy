#!/usr/bin/env python3
"""Execute dicom-validator's ConditionParser on condition texts taken from its own
unit tests and from patterns described in its documentation.

dict_info is built from pydicom's bundled data dictionary (tag -> name/vr/vm),
which is the shape the parser consumes; this avoids downloading a DICOM edition.
"""
import json
from pydicom.datadict import DicomDictionary
from dicom_validator.spec_reader.condition_parser import ConditionParser

dict_info = {}
for tag, (vr, vm, name, retired, keyword) in DicomDictionary.items():
    t = f"({tag >> 16:04X},{tag & 0xFFFF:04X})"
    dict_info[t] = {"name": name, "vr": vr, "vm": vm, "prop": retired}

p = ConditionParser(dict_info)
texts = [
    # simple, parsable
    "Required if VOI LUT Sequence (0028,3010) is not present.",
    # AND with an unparsable natural-language conjunct (from the project's tests)
    "Required if the image is reconstructed from a system with multiple X-Ray "
    "sources and Multi-energy CT Acquisition (0018,9361) is NO or is absent.",
    # OR with an unparsable disjunct (constructed)
    "Required if Multi-energy CT Acquisition (0018,9361) is YES or the Patient is an animal.",
    # purely descriptive condition (documentation example)
    "Required if the Patient is an animal.",
    # empty description
    "",
]
for t in texts:
    c = p.parse(t)
    print(json.dumps({"text": t[:90], "type": c.type.value if hasattr(c.type, 'value') else str(c.type),
                      "tag": c.tag, "operator": getattr(c.operator, 'value', c.operator),
                      "values": c.values}))
