#ifndef SCRYPT_H
#define SCRYPT_H

void scrypt_hash(const char* input, char* output);
void scrypt_hash_ext(const char* input, char* output, char* scratchpad);

char* scratchpad_alloc();
void scratchpad_free(char* p);

#endif
