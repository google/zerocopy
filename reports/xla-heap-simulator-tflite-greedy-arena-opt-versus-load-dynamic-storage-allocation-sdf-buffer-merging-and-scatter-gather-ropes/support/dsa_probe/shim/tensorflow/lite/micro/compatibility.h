// Minimal shim: the upstream macro deletes operator delete for embedded builds.
#ifndef PROBE_SHIM_COMPATIBILITY_H_
#define PROBE_SHIM_COMPATIBILITY_H_
#define TF_LITE_REMOVE_VIRTUAL_DELETE
#endif
