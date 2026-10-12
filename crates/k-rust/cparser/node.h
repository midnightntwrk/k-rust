#ifndef NODE_H
#define NODE_H

#include <stddef.h>

typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE {
  char *filename;
  int first_line;
  int first_column;
  int last_line;
  int last_column;
  /* The span in bytes of the input, from the first byte to the byte after the last, that the
     scanner read for the located phrase; `krust_kore_literal_at` reads its text. */
  size_t first_offset;
  size_t last_offset;
};

#define YYLTYPE struct YYLTYPE

#include "parser.tab.h"

#include <stdbool.h>

typedef struct node {
  char *symbol;
  char *sort;
  bool str;
  size_t nchildren;
  bool hasLocation;
  YYLTYPE location;
  struct node *children[];
} node;

typedef union value_type {
  node *nterm;
} value_type;

/* How a token's text gives the code points of its KORE string literal. */
enum krust_token_kind {
  /* The characters of the text. */
  KRUST_TOKEN_TEXT,
  /* The characters a K String literal writes. */
  KRUST_TOKEN_STRING,
  /* The bytes a K Bytes literal writes after its leading `b`, each the code point of its value. */
  KRUST_TOKEN_BYTES,
};

/* The KORE string literal of the code points the `length` bytes at `text` give by `kind`, or
   NULL when they are not a literal of that kind; `*error` is then a message naming `sort`. The
   text may hold NUL bytes: U+0000 is a character like any other. */
char *krust_kore_literal(
    const char *text, size_t length, enum krust_token_kind kind, const char *sort, char **error);

/* Append the `length` bytes at `text`, which the scanner read next, to the input read so far,
   and set the byte span of `location` to the place they take in it. */
void krust_read(YYLTYPE *location, const char *text, size_t length);

/* `krust_kore_literal` of the input text the byte span of `location` covers: the text of a token,
   or of the phrase a token subsort reads. */
char *krust_kore_literal_at(
    const YYLTYPE *location, enum krust_token_kind kind, const char *sort, char **error);

#endif
