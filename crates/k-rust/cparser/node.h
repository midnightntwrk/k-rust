#ifndef NODE_H
#define NODE_H

typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE {
  char *filename;
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};

#define YYLTYPE struct YYLTYPE

#include "parser.tab.h"

#include <stdbool.h>
#include <stddef.h>

typedef struct node {
  char *symbol;
  char *sort;
  bool str;
  /* The text a token production read, on the `\dv` node of a token or of a token subsort, which
     decodes it by its own sort; NULL on every other node. */
  char *token;
  size_t nchildren;
  bool hasLocation;
  YYLTYPE location;
  struct node *children[];
} node;

typedef union value_type {
  char *token;
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

/* The KORE string literal of the code points `token` gives by `kind`, or NULL when `token` is not
   a literal of that kind; `*error` is then a message naming `sort`. */
char *krust_kore_literal(
    const char *token, enum krust_token_kind kind, const char *sort, char **error);

#endif
