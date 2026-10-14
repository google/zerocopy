#!/usr/bin/env python3
"""Original finite illustration; this is not an upstream verified parser."""
import json
import sys

sys.dont_write_bytecode = True


def encode(value):
    assert type(value) is int and 0 <= value < 256
    return bytes((1, value))


def decode_prefix(data):
    if len(data) < 2 or data[0] != 1:
        return None
    return data[1]


def decode_complete(data):
    return decode_prefix(data) if len(data) == 2 else None


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate key')
        result[key] = value
    return result


def main():
    for value in range(256):
        data = encode(value)
        assert decode_prefix(data) == value
        assert decode_complete(data) == value
    for malformed in [b'', b'\x01', b'\x02\x00']:
        assert decode_prefix(malformed) is None
        assert decode_complete(malformed) is None
    extra = encode(42) + b'\xff'
    assert decode_prefix(extra) == 42
    assert decode_complete(extra) is None
    duplicate = '{"id":1,"id":2}'
    assert json.loads(duplicate) == {'id': 2}
    try:
        json.loads(duplicate, object_pairs_hook=no_duplicate_keys)
    except ValueError as exc:
        assert str(exc) == 'duplicate key'
        strict_rejects_duplicate = True
    else:
        raise AssertionError('strict decoder failed to reject duplicate keys')
    print(json.dumps({
        'scope': 'original finite illustration, no upstream theorem or executable claim',
        'value_domain': 256,
        'both_decoders_invert_canonical_encoder': True,
        'prefix_decoder_accepts_trailing_bytes': True,
        'complete_decoder_rejects_trailing_bytes': True,
        'malformed_specimens_rejected': 3,
        'stdlib_json_duplicate_value': {'id': 2},
        'local_strict_decoder_rejects_duplicate': strict_rejects_duplicate,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
