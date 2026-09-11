#define _GNU_SOURCE

#include <malloc.h>
#include <stddef.h>
#include <string.h>
#include <unistd.h>

extern void __libc_free(void *pointer);

static const unsigned char marker[32] = {
    0x91, 0x02, 0xa3, 0x14, 0xb5, 0x26, 0xc7, 0x38,
    0xd9, 0x4a, 0xeb, 0x5c, 0xfd, 0x6e, 0x8f, 0x70,
    0x81, 0xf2, 0x63, 0xd4, 0x45, 0xb6, 0x27, 0x98,
    0x09, 0x7a, 0xcb, 0x3c, 0xad, 0x1e, 0xef, 0x50,
};

static const char finding[] =
    "AUTHORITY_KEY_REMANENCE: marker reached free without clearing\n";

void free(void *pointer) {
    if (pointer != NULL) {
        size_t length = malloc_usable_size(pointer);
        if (length >= sizeof(marker)) {
            unsigned char *bytes = pointer;
            for (size_t offset = 0; offset <= length - sizeof(marker); ++offset) {
                if (memcmp(bytes + offset, marker, sizeof(marker)) == 0) {
                    ssize_t ignored =
                        write(STDERR_FILENO, finding, sizeof(finding) - 1);
                    (void)ignored;
                    break;
                }
            }
        }
    }
    __libc_free(pointer);
}
