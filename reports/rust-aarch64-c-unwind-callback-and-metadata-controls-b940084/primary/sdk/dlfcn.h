/*
 * Copyright (c) 2004-2026 Apple Inc. All rights reserved.
 *
 * @APPLE_LICENSE_HEADER_START@
 * 
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this
 * file.
 * 
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 * 
 * @APPLE_LICENSE_HEADER_END@
 */

/*
  Based on the dlcompat work done by:
		Jorge Acereda  <jacereda@users.sourceforge.net> &
		Peter O'Gorman <ogorman@users.sourceforge.net>
*/

#ifndef _DLFCN_H_
#define _DLFCN_H_

#include <sys/cdefs.h>

#if !defined(_POSIX_C_SOURCE) || (_POSIX_C_SOURCE >= 202405L) || defined(_DARWIN_C_SOURCE)
#include <stdbool.h>
#include <Availability.h>

#define __DYLDDL_UNAVAILABLE       __API_UNAVAILABLE(driverkit)

#define __DYLDDL_DLSYM_UNAVAILABLE __API_UNAVAILABLE(driverkit)


#ifdef __cplusplus
extern "C" {
#endif

/*!
 * Structure filled in by dladdr().
 *
 * ```C
 *   struct Dl_info {
 *       const char*  dli_fname;
 *       void*        dli_fbase;
 *       const char*  dli_sname;
 *       void*        dli_saddr;
 *   };
 * ```
 *
 * This structure contains information about the nearest symbol to a given address.
 * - Field dli_fname: The pathname of the mach-o image containing the address.
 * - Field dli_fbase: Load address of mach-o image containing the address.
 * - Field dli_sname: Name of nearest symbol.
 * - Field dli_saddr: Address of nearest symbol.
 */
typedef struct dl_info {
        const char* dli_fname;
        void*       dli_fbase;
        const char* dli_sname;
        void*       dli_saddr;
} Dl_info;
typedef struct dl_info Dl_info_t; /* POSIX 2024 */

/*!
 * Returns image and symbol information for an address.
 *
 * This function queries dyld (the dynamic linker) for information about the
 * image containing the specified address. For a given address in a mach-o image,
 * the function finds the closest symbol whose address is less than or equal to
 * the given address.
 *
 * - Parameter addr: The address to query.
 * - Parameter info: A pointer to a `Dl_info` structure that will be filled in with information
 *                   about the nearest symbol. The structure contains the pathname of the image,
 *                   its load address, the name of the nearest symbol, and the address of that symbol.
 *
 * - Returns: Returns non-zero if the address lies within a mapped image, zero otherwise.
 *            If no symbol was found, but the address is within a mapped image, the symbol
 *            information (dli_sname and dli_saddr) will be NULL
 *            and the image information (dli_fname and dli_fbase) will be filled in.
 *
 * > Note: The name `Dl_info_t` exists to match the new POSIX 2024 standard.
 *
 * > Note: This function does not follow Unix tradition. It returns zero as an indication of failure.
 *         Think of it as returning a `bool` where true means information for `addr` was returned.
 *
 * > Note: The strings returned are owned by dyld and do not need to be released/freed.  Though
 *         they will become invalid if the image is unloaded.
 */
extern int dladdr(const void*, Dl_info*);

#ifdef __cplusplus
}
#endif

#else
#define __DYLDDL_UNAVAILABLE
#define __DYLDDL_DLSYM_UNAVAILABLE
#endif /* not POSIX */

#ifdef __cplusplus
extern "C" {
#endif

/*!
 * Decrements the reference count on a dynamic library.
 *
 * When the reference count for a particular dynamic library becomes zero,
 * the dynamic library may be unloaded.
 *
 * - Parameter handle: A handle obtained by a previous call to dlopen().
 *
 * - Returns: Returns zero on success, or -1 if the handle is invalid or an error occurred.
 *            If an error occurred, a human readable string describing the error can be
 *            retrieved by calling dlerror().
 *
 * > Note: There are a couple of cases in which a dynamic library will never be unloaded:
 * > * the main executable directly or indirectly links against it
 * > * the dynamic library is in dyld's shared cache
 * > * the dynamic library has thread-local variables
 * > * the dynamic library contains Objective-C classes.
 */
extern int dlclose(void*) __DYLDDL_UNAVAILABLE;

/*!
 * Returns a human readable string describing the most recent error on the current thread.
 *
 * This function returns a null-terminated character string describing the last
 * error that occurred during a call to dlopen(), dlsym(), or dlclose() on this thread.
 * If no such error has occurred, dlerror() returns a null pointer. After each call
 * to dlerror(), the error string is reset.
 *
 * - Returns: A string describing the last dlopen/dlclose/dlsym error on this thread,
 *            or NULL if no error has occurred since the thread was started or
 *            since dlerror() was last called.
 *
 * > Note: You only get the error string once. Calling dlerror() twice in a row will
 *         result in the second call returning NULL.
 *
 */
extern char* dlerror(void) __DYLDDL_UNAVAILABLE;

/*!
 * Loads a dynamic library and returns a handle that can be used with dlsym() or dlclose().
 *
 * This function examines the mach-o file specified by path. If the file is compatible
 * with the current process and has not already been loaded into the process, it is
 * loaded and linked (which means recusively loading libraries it depends on).
 * After being linked, and before returning, any static initializers
 * are run and any Objective-C class or methods are registered with the ObjC runtime.
 * A second call to dlopen() that resolves to the same path will not load a second copy,
 * instead it just returns the existing handle, and increments that handles reference count.
 *
 * In general, dyld does not search for dylibs.  Dylibs are specified via a
 * full path, either as a static dependent dylib in a mach-o file, or as a path
 * passed to dlopen() , But during development the env vars `DYLD_LIBRARY_PATH`
 * and `DYLD_FRAMEWORK_PATH` can be used to override the specified path and look
 * for the leaf framework/dylib name in the specified directories.
 *
 * For dlopen(), when the path does not contain a slash character (i.e. it is just a leaf name),
 * dlopen() will do searching.  If `DYLD_LIBRARY_PATH` was set at launch, dyld
 * will first look in that directory.  Next, if the calling mach-o file or the
 * main executable specify an `LC_RPATH`, then dyld will look in those
 * directories. Next, if the process is unrestricted, dyld will search in the
 * current working directory. Lastly, for old binaries, dyld will try some
 * fallbacks.  If `DYLD_FALLBACK_LIBRARY_PATH` was set at launch, dyld will
 * search in those directories, otherwise, dyld will look in /usr/local/lib/
 * (if the process is unrestricted), and then in /usr/lib/.  This behavior
 * with dlopen of a leaf name is for historic compatibility.  You should strive
 * to use full paths (e.g. `dlopen("/usr/lib/libz.dylib", 0)`).
 *
 * When path looks like a framework path (e.g. /stuff/Foo.framework/Foo), if
 * `DYLD_FRAMEWORK_PATH` was set at launch, dyld will first look in that
 * directory for the framework partial path (e.g. Foo.framework/Foo). Next,
 * dyld will try the supplied path as-is (using current working directory for
 * relative paths).  Lastly, for old binaries, dyld will try some fallbacks.
 * If `DYLD_FALLBACK_FRAMEWORK_PATH` was set at launch, dyld will search those
 * directories.  Otherwise, it will search /Library/Frameworks (on macOS if
 * process is unrestricted), then /System/Library/Frameworks.
 *
 * When the path contains a slash but is not a framework path (i.e. a full path or
 * a partial path to a dylib), dlopen() first looks in (if set) in
 * `DYLD_LIBRARY_PATH` (with leaf part from path ).  Next, dyld tries the
 * supplied path (using current working directory for relative paths (but only
 * for unrestricted processes)).  Lastly, for older binaries, dyld will try
 * fallbacks.  If `DYLD_FALLBACK_LIBRARY_PATH` was set at launch, dyld will
 * search in those directories, otherwise, dyld will look in /usr/local/lib/
 * (if the process is unrestricted), and then in /usr/lib/.
 *
 * If you want to find a dylib via the dynamic run path, use @rpath (e.g.
 * `dlopen("@rpath/libfoo.dylib",RTLD_GLOBAL)`),
 *
 * - Parameter path: The path to a mach-o file. If path is NULL, dlopen() returns a handle
 *                   equivalent to RTLD_DEFAULT.
 * - Parameter mode: The mode to use when opening the library. This should be one or more of
 *                   RTLD_LAZY, RTLD_NOW, RTLD_LOCAL, RTLD_GLOBAL, RTLD_NOLOAD, RTLD_NODELETE,
 *                   or RTLD_FIRST.
 *
 * - Returns: A handle that can be used with dlsym() or dlclose(). If the library cannot be loaded,
 *            or an error occurs during loading, dlopen() returns NULL and dlerror() can be called
 *            to retrieve an error message.
 *
 * The `mode` flags are:
 *  * RTLD_LAZY     - The default
 *  * RTLD_NOW      - For old binaries, forces lazy symbols to be bound immediately. Lazy symbol
 *                    binding no longer exists with chained fixups, so this is moot.
 *  * RTLD_LOCAL    - Blocks symbols from being found by `dlsym(RTLD_DEFAULT)`
 *  * RTLD_GLOBAL   - The Default.  Allows symbols to be found by `dlsym(RTLD_DEFAULT)`
 *  * RTLD_NOLOAD   - If the requested image is not already loaded, return NULL. If is is already
 *                    loaded, bump the ref-count and return the handle.
 *  * RTLD_NODELETE - Never unmap the image.
 *  * RTLD_FIRST    - Causes dlsym() on the returned handle to only search that image and not continue
 *                    searching as it normally does if the requrested handle does not contain the symbol.
 *
 * > Note: On Apple platforms most OS dylibs are combined into the dyld cache and
 *         do not exist on disk. Therefore, calling stat() to preflight if an OS dylib
 *         exists won't work.
 *
 * > Note: You can run with `DYLD_PRINT_SEARCHING=1` to see all paths dyld tries (e.g. @rpath expansions).
 *
 * > Note: There are many security mechanisms that will disable dyld from using `DYLD_` env vars
 *         to prevent "dylib hijacking".
 *
 * > Note: There are no configuration files in the OS to control dlopen searching.
 *
 * > Note: Apple platforms use "universal" files to combine multiple architecture support into one file.
 *         This means there is not separate directories or search paths for each architecture.
 *
 */
extern void* dlopen(const char*, int) __DYLDDL_UNAVAILABLE;

/*!
 * Returns the address of a named symbol in a dynamic library.
 *
 * This function returns the address of the code or data location specified by the
 * null-terminated character string symbol. Which libraries and bundles are searched
 * depends on the handle parameter.
 *
 * - Parameter handle: A handle returned by dlopen(), or one of the special `RTLD_` values.
 * - Parameter symbol: The symbol name to look up.
 *
 * - Returns: The address of the symbol, or NULL if the symbol cannot be found. If an error occurs,
 *            dlerror() can be called to retrieve an error message.
 *
 * > Note: The special handles are:
 * > * RTLD_DEFAULT   - searches all mach-o images in the process in the order they were loaded.
 * > * RTLD_NEXT      - searches mach-o images that were loaded after the one calling dlsym().
 * > * RTLD_SELF      - searches the image calling dlsym() and those loaded after it.
 * > * RTLD_MAIN_ONLY - searches only the main executable.
 *
 * > Note: If the requested symbol name is not in the requested handle, dlsym() will continue
 *         recursively searching in libraries that the handle's library links with.  This can make
 *         looking up symbols likely to be missing very slow. To avoid that cost, use `RTLD_FIRST`
 *         with dlopen() to mark the handle "search shallow".
 *
 * > Note: The symbol name string passed to dlsym() is the C name (e.g. `"malloc"`), even though the
 *         internal mach-o symbol name has a leading underscore (e.g. `"_malloc"`)
 *
 * > Note: For processes running with PAC (arm64e), if the symbol found is a function (i.e not data)
 *         the return pointer will be PAC signed with zero-diversity.
 *
 * > Note: `RTLD_DEFAULT` is very expensive and should be avoided. It potentially searches every
 *         dynamic library in the process, which could mean search 1000+ libraries.
 *
 */
extern void* dlsym(void*, const char*) __DYLDDL_DLSYM_UNAVAILABLE;

#if !defined(_POSIX_C_SOURCE) || defined(_DARWIN_C_SOURCE)
/*!
 * Determines if a dynamic library or bundle can be loaded.
 *
 * This function examines the mach-o file specified by path to determine if it is
 * compatible with the current process and can be loaded. It returns true if the
 * file exists, is accessible, is of the correct Mach-O format, and is compatible.
 * Unlike dlopen(), this function does not actually load the library or cause any
 * of its initializer functions to be called.
 *
 * - Parameter path: The path to a mach-o file to examine.
 *
 * - Returns: Returns true if the image appears to be compatible and can be loaded,
 *            false otherwise. If false, dlerror() can be called to retrieve an error message.
 *
 * > Note: The function was created in the Mac PowerPC-to-Intel transition for apps that needed
 *         to build menus showing available plug-ins. Every other use is probably wrong.
 *         If you want to load a library, just call dlopen().
 *
 */
extern bool dlopen_preflight(const char*) __API_AVAILABLE(macos(10.5), ios(2.0)) __DYLDDL_UNAVAILABLE;
#endif /* not POSIX */


/*
 * Flags for dlopen().
 */
#define RTLD_LAZY	0x1
#define RTLD_NOW	0x2
#define RTLD_LOCAL	0x4
#define RTLD_GLOBAL	0x8

#if !defined(_POSIX_C_SOURCE) || defined(_DARWIN_C_SOURCE)
#define RTLD_NOLOAD	  0x10
#define RTLD_NODELETE 0x80
#define RTLD_FIRST    0x100 

/*
 * Special handle values for dlsym().
 */
#define    RTLD_NEXT       ((void *) -1)    /* Search subsequent objects. */
#define    RTLD_DEFAULT    ((void *) -2)    /* Use default search algorithm. */
#define    RTLD_SELF       ((void *) -3)    /* Search this and subsequent objects */
#define    RTLD_MAIN_ONLY  ((void *) -5)    /* Search main executable only */
#endif /* not POSIX */

#ifdef __cplusplus
}
#endif

#endif /* _DLFCN_H_ */
