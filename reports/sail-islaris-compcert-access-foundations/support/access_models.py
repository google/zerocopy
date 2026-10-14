"""Finite predicate-separation fixtures, not execution of the named models."""
import json


def all_bytes(region, addr, width):
    return width > 0 and all(addr + offset in region for offset in range(width))


def run():
    addr = 4096
    byte_domain = set(range(addr, addr + 64))
    mapped = set(byte_domain)
    readable = set(byte_domain)
    writable = set(range(addr, addr + 8))
    cases = {
        "scalar8": {"map_defined": all_bytes(byte_domain, addr, 8), "vm_mapped": all_bytes(mapped, addr, 8), "readable": all_bytes(readable, addr, 8), "writable": all_bytes(writable, addr, 8)},
        "vector32": {"map_defined": all_bytes(byte_domain, addr, 32), "vm_mapped": all_bytes(mapped, addr, 32), "readable": all_bytes(readable, addr, 32), "writable": all_bytes(writable, addr, 32)},
        "crossing64_at_plus8": {"map_defined": all_bytes(byte_domain, addr + 8, 64), "vm_mapped": all_bytes(mapped, addr + 8, 64), "readable": all_bytes(readable, addr + 8, 64), "writable": all_bytes(writable, addr + 8, 64)},
        "expired_logical_authority": {"map_defined": True, "vm_mapped": True, "readable": True, "writable": True, "live_authority": False},
    }
    assert cases["vector32"]["map_defined"] and not cases["vector32"]["writable"]
    assert cases["scalar8"]["writable"]
    assert not cases["crossing64_at_plus8"]["map_defined"]
    return {"scope": "explicit finite fixtures; no CompCert/Sail/Islaris execution or Rust alias-model proof", "cases": cases}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
