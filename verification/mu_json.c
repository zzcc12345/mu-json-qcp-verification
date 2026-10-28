/**
 * MIT License
 *
 * Copyright (c) 2021-2024 R. D. Poor <rdpoor@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

typedef unsigned char uint8_t;
typedef enum {
    MU_JSON_ERR_NONE = 0, MU_JSON_ERR_BAD_FORMAT = -1, MU_JSON_ERR_INCOMPLETE = -2, MU_JSON_ERR_NO_ENTITIES = -3, MU_JSON_ERR_STRAY_INPUT = -4, MU_JSON_ERR_NOT_ENOUGH_TOKENS = -5, MU_JSON_ERR_BAD_ARGUMENT = -6, MU_JSON_ERR_TOO_DEEP = -7, MU_JSON_ERR_NO_MULTIBYTE = -8, MU_JSON_ERR_INTERNAL = -9} mu_json_err_t;
typedef enum {
    MU_JSON_TOKEN_TYPE_UNKNOWN, MU_JSON_TOKEN_TYPE_ARRAY, MU_JSON_TOKEN_TYPE_OBJECT, MU_JSON_TOKEN_TYPE_STRING, MU_JSON_TOKEN_TYPE_NUMBER, MU_JSON_TOKEN_TYPE_INTEGER, MU_JSON_TOKEN_TYPE_TRUE, MU_JSON_TOKEN_TYPE_FALSE, MU_JSON_TOKEN_TYPE_NULL} mu_json_token_type_t;
typedef struct {
    const char *str;
    unsigned int packed_fields;
} mu_json_token_t;
int mu_json_parse_str(const char *str,
                      mu_json_token_t *token_store, int max_tokens);
int mu_json_parse_buffer(const uint8_t *input, int input_len,
                         mu_json_token_t *token_store, int max_tokens);
const char *mu_json_error_name(mu_json_err_t errnum);
const char *mu_json_token_string(mu_json_token_t *token);
int mu_json_token_string_length(mu_json_token_t *token);
mu_json_token_type_t mu_json_token_type(mu_json_token_t *token);
int mu_json_token_level(mu_json_token_t *token);
_Bool mu_json_token_is_first(mu_json_token_t *token);
_Bool mu_json_token_is_last(mu_json_token_t *token);
mu_json_token_t *mu_json_find_prev_token(mu_json_token_t *token);
mu_json_token_t *mu_json_find_next_token(mu_json_token_t *token);
mu_json_token_t *mu_json_find_root_token(mu_json_token_t *token);
mu_json_token_t *mu_json_find_parent_token(mu_json_token_t *token);
mu_json_token_t *mu_json_find_child_token(mu_json_token_t *token);
mu_json_token_t *mu_json_find_prev_sibling_token(mu_json_token_t *token);
mu_json_token_t *mu_json_find_next_sibling_token(mu_json_token_t *token);
typedef unsigned int size_t;
size_t strlen(const char *s);
void *memset(void *s, int c, size_t n);
typedef struct parser {
    const char *str;
    int str_len;
    int str_pos;
    mu_json_token_t *token_store;
    int max_tokens;
    int token_count;
    int level;
    mu_json_token_t *current_token;
} parser_t;
static const char *s_error_names[10] = {
    "MU_JSON_ERR_NONE", "MU_JSON_ERR_BAD_FORMAT", "MU_JSON_ERR_INCOMPLETE", "MU_JSON_ERR_NO_ENTITIES", "MU_JSON_ERR_STRAY_INPUT", "MU_JSON_ERR_NOT_ENOUGH_TOKENS", "MU_JSON_ERR_BAD_ARGUMENT", "MU_JSON_ERR_TOO_DEEP", "MU_JSON_ERR_NO_MULTIBYTE", "MU_JSON_ERR_INTERNAL"};
static const char *s_token_type_names[9] = {
    "MU_JSON_TOKEN_TYPE_UNKNOWN", "MU_JSON_TOKEN_TYPE_ARRAY", "MU_JSON_TOKEN_TYPE_OBJECT", "MU_JSON_TOKEN_TYPE_STRING", "MU_JSON_TOKEN_TYPE_NUMBER", "MU_JSON_TOKEN_TYPE_INTEGER", "MU_JSON_TOKEN_TYPE_TRUE", "MU_JSON_TOKEN_TYPE_FALSE", "MU_JSON_TOKEN_TYPE_NULL"};
inline static _Bool at_eos(parser_t *p)
/*@ With pos len
    Require INT_MIN <= pos && pos <= INT_MAX && INT_MIN <= len && len <= INT_MAX &&
            p->str_pos == pos && p->str_len == len
    Ensure p->str_pos == pos && p->str_len == len &&
           ((__return == 1 && pos >= len) || (__return == 0 && pos < len))
*/
{ return p->str_pos >= p->str_len; }
inline static char peek_char(parser_t *p)
/*@ With s pos n (l : list Z)
    Require 0 <= pos && pos < n && n <= INT_MAX &&
            p->str == s && p->str_pos == pos && CharArray::full(s, n, l)
    Ensure __return == Znth(pos, l, 0) &&
           p->str == s && p->str_pos == pos && CharArray::full(s, n, l)
*/
{ return p->str[p->str_pos]; }
inline static char get_char(parser_t *p)
/*@ With s pos n (l : list Z)
    Require 0 <= pos && pos < n && n <= INT_MAX &&
            p->str == s && p->str_pos == pos && CharArray::full(s, n, l)
    Ensure __return == Znth(pos, l, 0) &&
           p->str == s && p->str_pos == pos + 1 && CharArray::full(s, n, l)
*/
{ char ch = p->str[p->str_pos]; p->str_pos = p->str_pos + 1; return ch; }
inline static const char *ref_char(parser_t *p)
/*@ With s pos n (l : list Z)
    Require 0 <= pos && pos <= n && n <= INT_MAX &&
            p->str == s && p->str_pos == pos && CharArray::full(s, n, l)
    Ensure __return == s + pos &&
           p->str == s && p->str_pos == pos && CharArray::full(s, n, l)
*/
{ return &p->str[p->str_pos]; }
inline static _Bool is_digit(char ch)
/*@ Require -128 <= ch && ch <= 255
    Ensure (__return == 1 && 48 <= ch && ch <= 57) ||
           (__return == 0 && (ch < 48 || 57 < ch))
*/
{ return (ch >= 48) && (ch <= 57); }
static inline _Bool token_is_null(mu_json_token_t *token)
/*@ Require emp
    Ensure (__return == 1 && token == 0) || (__return == 0 && token != 0)
*/
{
    return token == ((void *)0);
}
static inline _Bool token_is_first(mu_json_token_t *token)
/*@ With w
    Require 0 <= w && w <= 4294967295 && token->packed_fields == w
    Ensure ((__return == 1 && ((w >> 20) & 2047) == 0) || (__return == 0 && ((w >> 20) & 2047) != 0)) && token->packed_fields == w
*/
{
    return ((int)((token->packed_fields >> 20) & 2047U)) == 0;
}
static inline _Bool token_is_last(mu_json_token_t *token)
/*@ With w
    Require 0 <= w && w <= 4294967295 && token->packed_fields == w
    Ensure __return == ((w >> 31) & 1) && token->packed_fields == w
*/
{
    return ((int)((token->packed_fields >> 31) & 1U));
}
static void skip_whitespace(parser_t *p);
static void parser_reset(parser_t *p);
static int parse_json(const char *str, int str_len,
                      mu_json_token_t *token_store, int max_tokens);
static mu_json_err_t parse_element(parser_t *p);
static mu_json_err_t parse_string(parser_t *p);
static mu_json_err_t parse_number(parser_t *p);
static mu_json_err_t parse_literal(parser_t *p, const char *literal,
                                   mu_json_token_type_t type);
static mu_json_err_t parse_object(parser_t *p);
static mu_json_err_t parse_array(parser_t *p);
static _Bool is_hex(char ch);
static mu_json_token_t *alloc_token(parser_t *p);
static mu_json_token_t *init_token(parser_t *p, mu_json_token_type_t type);
static void finalize_token(parser_t *p, mu_json_token_t *tok);
static void set_token_string(mu_json_token_t *token, const char *string);
static const char *get_token_string(mu_json_token_t *token);
static void set_token_string_length(mu_json_token_t *token, int string_length);
static void set_token_type(mu_json_token_t *token,
                           mu_json_token_type_t token_type);
static void set_token_level(mu_json_token_t *token, int level);
static void set_token_is_last(mu_json_token_t *token, _Bool is_last);
static const char *token_type_name(mu_json_token_type_t type);
static void log_input_state(const char *message, parser_t *p);
static mu_json_token_t *find_sibling(mu_json_token_t *token,
                                     mu_json_token_t *(*m)(mu_json_token_t *));
int mu_json_parse_str(const char *str, mu_json_token_t *token_store,
                      int max_tokens) {
    return parse_json(str, strlen(str), token_store, max_tokens);
}
int mu_json_parse_buffer(const uint8_t *input, int input_len,
                         mu_json_token_t *token_store, int max_tokens) {
    return parse_json((const char *)input, input_len, token_store, max_tokens);
}
const char *mu_json_error_name(mu_json_err_t errnum) {
    errnum = -errnum;
    if (errnum < 0) {
        return s_error_names[0];
    } else if (errnum >= (sizeof(s_error_names) / sizeof(s_error_names[0]))) {
        return "MU_JSON_ERR_UNKNOWN";
    } else {
        return s_error_names[errnum];
    }
}
const char *mu_json_token_string(mu_json_token_t *token)
/*@ With s
    Require (token == 0 && s == 0 && emp) || (token != 0 && token->str == s)
    Ensure __return == s &&
           ((token == 0 && s == 0 && emp) || (token != 0 && token->str == s))
*/
{
    if (token_is_null(token)) {
        return ((void *)0);
    } else {
        return token->str;
    }
}
int mu_json_token_string_length(mu_json_token_t *token)
/*@ With w
    Require (token == 0 && emp) || (token != 0 && 0 <= w && w <= 4294967295 && token->packed_fields == w)
    Ensure (token == 0 && __return == -1 && emp) ||
           (token != 0 && __return == ((w >> 0) & 65535) && token->packed_fields == w)
*/
{
    if (token_is_null(token)) {
        return -1;
    } else {
        return ((int)((token->packed_fields >> 0) & 65535U));
    }
}
mu_json_token_type_t mu_json_token_type(mu_json_token_t *token)
/*@ With w
    Require (token == 0 && emp) || (token != 0 && 0 <= w && w <= 4294967295 && token->packed_fields == w)
    Ensure (token == 0 && __return == 0 && emp) ||
           (token != 0 && __return == ((w >> 16) & 15) && token->packed_fields == w)
*/
{
    if (token_is_null(token)) {
        return MU_JSON_TOKEN_TYPE_UNKNOWN;
    } else {
        return ((int)((token->packed_fields >> 16) & 15U));
    }
}
int mu_json_token_level(mu_json_token_t *token)
/*@ With w
    Require (token == 0 && emp) || (token != 0 && 0 <= w && w <= 4294967295 && token->packed_fields == w)
    Ensure (token == 0 && __return == -1 && emp) ||
           (token != 0 && __return == ((w >> 20) & 2047) && token->packed_fields == w)
*/
{
    if (token_is_null(token)) {
        return -1;
    } else {
        return ((int)((token->packed_fields >> 20) & 2047U));
    }
}
_Bool mu_json_token_is_first(mu_json_token_t *token)
/*@ With w
    Require (token == 0 && emp) || (token != 0 && 0 <= w && w <= 4294967295 && token->packed_fields == w)
    Ensure (token == 0 && __return == 0 && emp) ||
           (token != 0 && ((__return == 1 && ((w >> 20) & 2047) == 0) || (__return == 0 && ((w >> 20) & 2047) != 0)) && token->packed_fields == w)
*/
{
    if (token_is_null(token)) {
        return 0;
    } else {
        return token_is_first(token);
    }
}
_Bool mu_json_token_is_last(mu_json_token_t *token)
/*@ With w
    Require (token == 0 && emp) || (token != 0 && 0 <= w && w <= 4294967295 && token->packed_fields == w)
    Ensure (token == 0 && __return == 0 && emp) ||
           (token != 0 && __return == ((w >> 31) & 1) && token->packed_fields == w)
*/
{
    if (token_is_null(token)) {
        return 0;
    } else {
        return token_is_last(token);
    }
}
mu_json_token_t *mu_json_find_root_token(mu_json_token_t *token) {
    if (token_is_null(token))
        return ((void *)0);
    while (!token_is_first(token)) {
        token = &token[-1];
    }
    return token;
}
mu_json_token_t *mu_json_find_next_token(mu_json_token_t *token) {
    if (token_is_null(token) || token_is_last(token))
        return ((void *)0);
    return &token[1];
}
mu_json_token_t *mu_json_find_prev_token(mu_json_token_t *token) {
    if (token_is_null(token) || token_is_first(token))
        return ((void *)0);
    return &token[-1];
}
mu_json_token_t *mu_json_find_parent_token(mu_json_token_t *token) {
    if (token_is_null(token) || token_is_first(token))
        return ((void *)0);
    mu_json_token_t *current = token;
    int target_level = ((int)((token->packed_fields >> 20) & 2047U)) - 1;
    while (((int)((current->packed_fields >> 20) & 2047U)) > target_level) {
        current = mu_json_find_prev_token(current);
        if (token_is_null(current))
            return ((void *)0);
    }
    return current;
}
mu_json_token_t *mu_json_find_child_token(mu_json_token_t *token) {
    if (token_is_null(token) || token_is_last(token))
        return ((void *)0);
    mu_json_token_t *next = mu_json_find_next_token(token);
    if (token_is_null(next) || ((int)((next->packed_fields >> 20) & 2047U)) <= ((int)((token->packed_fields >> 20) & 2047U)))
        return ((void *)0);
    return next;
}
mu_json_token_t *mu_json_find_next_sibling_token(mu_json_token_t *token) {
    return find_sibling(token, mu_json_find_next_token);
}
mu_json_token_t *mu_json_find_prev_sibling_token(mu_json_token_t *token) {
    return find_sibling(token, mu_json_find_prev_token);
}
static void skip_whitespace(parser_t *p)
/*@ With s start n (l : list Z)
    Require 0 <= start && start <= n && n <= INT_MAX &&
            p->str == s && p->str_pos == start && p->str_len == n && CharArray::full(s, n, l)
    Ensure start <= p->str_pos && p->str_pos <= n && (forall (i : Z), (start <= i && i < p->str_pos) => (Znth(i, l, 0) == 32 || Znth(i, l, 0) == 9 || Znth(i, l, 0) == 10 || Znth(i, l, 0) == 13)) && (p->str_pos == n || (p->str_pos < n && !(Znth(p->str_pos, l, 0) == 32 || Znth(p->str_pos, l, 0) == 9 || Znth(p->str_pos, l, 0) == 10 || Znth(p->str_pos, l, 0) == 13))) &&
           p->str == s && p->str_len == n && CharArray::full(s, n, l)
*/
{
    /*@ Inv Assert p == p@pre && 0 <= start && start <= p->str_pos && p->str_pos <= n && n <= INT_MAX &&
          (forall (i : Z), (start <= i && i < p->str_pos) => (Znth(i, l, 0) == 32 || Znth(i, l, 0) == 9 || Znth(i, l, 0) == 10 || Znth(i, l, 0) == 13)) && p->str == s && p->str_len == n && CharArray::full(s, n, l)
    */
    while (!at_eos(p)) {
        char ch = peek_char(p);
        if ((ch == 32) || (ch == 9) || (ch == 10) || (ch == 13)) {
            get_char(p);
        } else {
            break;
        }
    }
}
static void parser_reset(parser_t *p) {
    mu_json_token_t *tokens = p->token_store;
    memset(tokens, 0, sizeof(mu_json_token_t) * p->max_tokens);
    p->str_pos = 0;
    p->token_count = 0;
    p->level = 0;
    p->current_token = ((void *)0);
}
static int parse_json(const char *str, int str_len,
                      mu_json_token_t *token_store, int max_tokens) {
    mu_json_err_t err;
    if (str == ((void *)0)) {
        return MU_JSON_ERR_BAD_ARGUMENT;
    } else if (token_store == ((void *)0)) {
        return MU_JSON_ERR_BAD_ARGUMENT;
    } else if (str_len == 0) {
        return MU_JSON_ERR_BAD_ARGUMENT;
    } else if (max_tokens == 0) {
        return MU_JSON_ERR_BAD_ARGUMENT;
    }
    parser_t parser = {
        .str = str,
        .str_len = str_len,
        .token_store = token_store,
        .max_tokens = max_tokens};
    parser_t *p = &parser;
    parser_reset(p);
    err = parse_element(p);
    if (err != MU_JSON_ERR_NONE) {
        return err;
    } else if (p->token_count == 0) {
        return MU_JSON_ERR_NO_ENTITIES;
    }
    skip_whitespace(p);
    if (!at_eos(p)) {
        return MU_JSON_ERR_STRAY_INPUT;
    }
    set_token_is_last(&p->token_store[p->token_count - 1], 1);
    return p->token_count;
}
static mu_json_err_t parse_element(parser_t *p) {
    mu_json_err_t err = MU_JSON_ERR_NONE;
    skip_whitespace(p);
    if (!at_eos(p)) {
        char ch = peek_char(p);
        if (ch == 34) {
            err = parse_string(p);
        } else if ((is_digit(ch) || ch == 45)) {
            err = parse_number(p);
        } else if (ch == 116) {
            err = parse_literal(p, "true", MU_JSON_TOKEN_TYPE_TRUE);
        } else if (ch == 102) {
            err = parse_literal(p, "false", MU_JSON_TOKEN_TYPE_FALSE);
        } else if (ch == 110) {
            err = parse_literal(p, "null", MU_JSON_TOKEN_TYPE_NULL);
        } else if (ch == 123) {
            err = parse_object(p);
        } else if (ch == 91) {
            err = parse_array(p);
        } else {
            if (ch & 0x80) {
                err = MU_JSON_ERR_NO_MULTIBYTE;
            } else {
                err = MU_JSON_ERR_BAD_FORMAT;
            }
        }
    }
    return err;
}
mu_json_err_t parse_string(parser_t *p) {
    if (at_eos(p) || peek_char(p) != 34) {
        return MU_JSON_ERR_INTERNAL;
    }
    mu_json_token_t *tok = init_token(p, MU_JSON_TOKEN_TYPE_STRING);
    if (tok == ((void *)0)) {
        return MU_JSON_ERR_NOT_ENOUGH_TOKENS;
    }
    get_char(p);
    while (!at_eos(p)) {
        char ch = peek_char(p);
        if (ch == 92) {
            get_char(p);
            if (at_eos(p)) {
                return MU_JSON_ERR_INCOMPLETE;
            }
            char escape_char = peek_char(p);
            if (escape_char == 34 || escape_char == 92 || escape_char == 47 ||
                escape_char == 98 || escape_char == 102 || escape_char == 110 ||
                escape_char == 114 || escape_char == 116) {
                get_char(p);
            } else if (escape_char == 117) {
                get_char(p);
                for (int i = 0; i < 4; i++) {
                    if (at_eos(p) || !is_hex(peek_char(p))) return MU_JSON_ERR_BAD_FORMAT;
                    get_char(p);
                }
            } else {
                return MU_JSON_ERR_BAD_FORMAT;
            }
        } else if (ch & 0x80) {
            return MU_JSON_ERR_NO_MULTIBYTE;
        } else if (ch < 0x20) {
            return MU_JSON_ERR_BAD_FORMAT;
        } else if (ch == 34) {
            break;
        } else {
            get_char(p);
        }
    }
    if (at_eos(p)) {
        return MU_JSON_ERR_INCOMPLETE;
    }
    if (peek_char(p) != 34) {
        return MU_JSON_ERR_INTERNAL;
    }
    get_char(p);
    finalize_token(p, tok);
    return MU_JSON_ERR_NONE;
}
static _Bool is_number_prefix(char ch)
/*@ Require -128 <= ch && ch <= 255
    Ensure (__return == 1 && (ch == 45 || (48 <= ch && ch <= 57))) ||
           (__return == 0 && ch != 45 && (ch < 48 || 57 < ch))
*/
{
    return (ch == 45) || ((ch >= 48) && (ch <= 57));
}
static mu_json_err_t parse_number(parser_t *p) {
    if (at_eos(p) || !is_number_prefix(peek_char(p))) {
        return MU_JSON_ERR_INTERNAL;
    }
    mu_json_token_t *tok = init_token(p, MU_JSON_TOKEN_TYPE_INTEGER);
    if (tok == ((void *)0)) {
        return MU_JSON_ERR_NOT_ENOUGH_TOKENS;
    }
    if (peek_char(p) == 45) {
        get_char(p);
    }
    if (at_eos(p)) {
        return MU_JSON_ERR_INCOMPLETE;
    }
    _Bool has_leading_zero = 0;
    if (!at_eos(p)) {
        char ch = peek_char(p);
        if (ch == 48) {
            has_leading_zero = 1;
            get_char(p);
        }
    }
    if (has_leading_zero && !at_eos(p)) {
        char ch = peek_char(p);
        if (ch == 48) {
            return MU_JSON_ERR_BAD_FORMAT;
        }
    }
    _Bool has_integer_part = 0;
    while (!at_eos(p)) {
        char ch = peek_char(p);
        if (ch >= 48 && ch <= 57) {
            has_integer_part = 1;
            get_char(p);
        } else {
            break;
        }
    }
    if (has_leading_zero && has_integer_part) {
        return MU_JSON_ERR_BAD_FORMAT;
    }
    if (!has_leading_zero && !has_integer_part) {
        return MU_JSON_ERR_BAD_FORMAT;
    }
    _Bool has_fractional_part = 0;
    if (!at_eos(p) && peek_char(p) == 46) {
        set_token_type(tok, MU_JSON_TOKEN_TYPE_NUMBER);
        get_char(p);
        while (!at_eos(p)) {
            char ch = peek_char(p);
            if (ch >= 48 && ch <= 57) {
                has_fractional_part = 1;
                get_char(p);
            } else {
                break;
            }
        }
        if (!has_fractional_part) {
            return MU_JSON_ERR_BAD_FORMAT;
        }
    }
    if (!at_eos(p) && (peek_char(p) == 101 || peek_char(p) == 69)) {
        set_token_type(tok, MU_JSON_TOKEN_TYPE_NUMBER);
        get_char(p);
        if (!at_eos(p) && (peek_char(p) == 43 || peek_char(p) == 45)) {
            get_char(p);
        }
        _Bool has_exponent_digits = 0;
        while (!at_eos(p)) {
            char ch = peek_char(p);
            if (ch >= 48 && ch <= 57) {
                has_exponent_digits = 1;
                get_char(p);
            } else {
                break;
            }
        }
        if (!has_exponent_digits) {
            return MU_JSON_ERR_BAD_FORMAT;
        }
    }
    finalize_token(p, tok);
    return MU_JSON_ERR_NONE;
}
static mu_json_err_t parse_literal(parser_t *p, const char *literal,
                                   mu_json_token_type_t type) {
    if (at_eos(p)) {
        return MU_JSON_ERR_INTERNAL;
    }
    int literal_len = strlen(literal);
    mu_json_token_t *tok = init_token(p, type);
    if (tok == ((void *)0)) {
        return MU_JSON_ERR_NOT_ENOUGH_TOKENS;
    }
    for (int i = 0; i < literal_len; i++) {
        if (at_eos(p)) {
            return MU_JSON_ERR_INCOMPLETE;
        } else if (get_char(p) != literal[i]) {
            return MU_JSON_ERR_BAD_FORMAT;
        }
    }
    finalize_token(p, tok);
    return MU_JSON_ERR_NONE;
}
mu_json_err_t find_and_skip(parser_t *p, char delimiter) {
    skip_whitespace(p);
    if (at_eos(p)) {
        return MU_JSON_ERR_BAD_FORMAT;
    }
    if (peek_char(p) != delimiter) {
        return MU_JSON_ERR_BAD_FORMAT;
    }
    get_char(p);
    skip_whitespace(p);
    if (at_eos(p)) {
        return MU_JSON_ERR_BAD_FORMAT;
    }
    return MU_JSON_ERR_NONE;
}
mu_json_err_t parse_object(parser_t *p) {
    mu_json_err_t err;
    if (at_eos(p) || peek_char(p) != 123) {
        return MU_JSON_ERR_INTERNAL;
    }
    mu_json_token_t *tok = init_token(p, MU_JSON_TOKEN_TYPE_OBJECT);
    if (tok == ((void *)0)) {
        return MU_JSON_ERR_NOT_ENOUGH_TOKENS;
    }
    p->level++;
    get_char(p);
    err = MU_JSON_ERR_NONE;
    _Bool first_pair = 1;
    while (1) {
        skip_whitespace(p);
        if (at_eos(p)) {
            break;
        }
        if (peek_char(p) == 125) {
            break;
        }
        if (!first_pair) {
            err = find_and_skip(p, 44);
            if (err != MU_JSON_ERR_NONE) {
                return err;
            }
        }
        first_pair = 0;
        err = parse_string(p);
        if (err != MU_JSON_ERR_NONE) {
            return err;
        }
        err = find_and_skip(p, 58);
        if (err != MU_JSON_ERR_NONE) {
            return err;
        }
        err = parse_element(p);
        if (err != MU_JSON_ERR_NONE) {
            return err;
        }
    }
    if (at_eos(p)) {
        return MU_JSON_ERR_INCOMPLETE;
    }
    if (peek_char(p) != 125) {
        return MU_JSON_ERR_INTERNAL;
    }
    get_char(p);
    p->level--;
    set_token_string_length(tok, ref_char(p) - get_token_string(tok));
    return MU_JSON_ERR_NONE;
}
mu_json_err_t parse_array(parser_t *p) {
    mu_json_err_t err;
    if (at_eos(p) || peek_char(p) != 91) {
        return MU_JSON_ERR_INTERNAL;
    }
    mu_json_token_t *tok = init_token(p, MU_JSON_TOKEN_TYPE_ARRAY);
    if (tok == ((void *)0)) {
        return MU_JSON_ERR_NOT_ENOUGH_TOKENS;
    }
    p->level++;
    get_char(p);
    _Bool first_element = 1;
    while (1) {
        skip_whitespace(p);
        if (at_eos(p)) {
            break;
        }
        if (peek_char(p) == 93) {
            break;
        }
        if (!first_element) {
            err = find_and_skip(p, 44);
            if (err != MU_JSON_ERR_NONE) {
                return err;
            }
        }
        first_element = 0;
        mu_json_err_t err = parse_element(p);
        if (err != MU_JSON_ERR_NONE) {
            return err;
        }
    }
    if (at_eos(p)) {
        return MU_JSON_ERR_INCOMPLETE;
    }
    if (peek_char(p) != 93) {
        return MU_JSON_ERR_INTERNAL;
    }
    get_char(p);
    p->level--;
    set_token_string_length(tok, ref_char(p) - get_token_string(tok));
    return MU_JSON_ERR_NONE;
}
static _Bool is_hex(char ch)
/*@ Require -128 <= ch && ch <= 255
    Ensure (__return == 1 && ((48 <= ch && ch <= 57) || (65 <= ch && ch <= 70) || (97 <= ch && ch <= 102))) ||
           (__return == 0 && (ch < 48 || 57 < ch) && (ch < 65 || 70 < ch) && (ch < 97 || 102 < ch))
*/
{
    return ((ch >= 48 && ch <= 57) || (ch >= 65 && ch <= 70) ||
            (ch >= 97 && ch <= 102));
}
static mu_json_token_t *alloc_token(parser_t *p) {
    if (p->token_count >= p->max_tokens) {
        return ((void *)0);
    } else {
        mu_json_token_t *tok = &p->token_store[p->token_count]; p->token_count = p->token_count + 1; return tok;
    }
}
static mu_json_token_t *init_token(parser_t *p, mu_json_token_type_t type) {
    mu_json_token_t *tok = alloc_token(p);
    if (tok == ((void *)0)) {
        return ((void *)0);
    }
    set_token_string(tok, ref_char(p));
    set_token_type(tok, type);
    set_token_level(tok, p->level);
    return tok;
}
static void finalize_token(parser_t *p, mu_json_token_t *tok) {
    set_token_string_length(tok, ref_char(p) - get_token_string(tok));
}
static void set_token_string(mu_json_token_t *token, const char *string)
/*@ Require undef_data_at(&(token->str))
    Ensure token->str == string
*/
{
    token->str = string;
}
static const char *get_token_string(mu_json_token_t *token)
/*@ With s
    Require token->str == s
    Ensure __return == s && token->str == s
*/
{
    return token->str;
}
static void set_token_string_length(mu_json_token_t *token, int string_length)
/*@ With w
    Require 0 <= w && w <= 4294967295 && INT_MIN <= string_length && string_length <= INT_MAX && token->packed_fields == w
    Ensure token->packed_fields == ((w & 4294901760) | ((string_length & 65535) << 0))
*/
{
    token->packed_fields = (token->packed_fields & 4294901760U) | ((((unsigned int)string_length) & 65535U) << 0);
}
static void set_token_type(mu_json_token_t *token,
                           mu_json_token_type_t token_type)
/*@ With w
    Require 0 <= w && w <= 4294967295 && INT_MIN <= token_type && token_type <= INT_MAX && token->packed_fields == w
    Ensure token->packed_fields == ((w & 4293984255) | ((token_type & 15) << 16))
*/
{
    token->packed_fields = (token->packed_fields & 4293984255U) | ((((unsigned int)token_type) & 15U) << 16);
}
static void set_token_level(mu_json_token_t *token, int level)
/*@ With w
    Require 0 <= w && w <= 4294967295 && INT_MIN <= level && level <= INT_MAX && token->packed_fields == w
    Ensure token->packed_fields == ((w & 2148532223) | ((level & 2047) << 20))
*/
{
    token->packed_fields = (token->packed_fields & 2148532223U) | ((((unsigned int)level) & 2047U) << 20);
}
static void set_token_is_last(mu_json_token_t *token, _Bool is_last)
/*@ With w
    Require 0 <= w && w <= 4294967295 && 0 <= is_last && is_last <= 1 && token->packed_fields == w
    Ensure token->packed_fields == ((w & 2147483647) | ((is_last & 1) << 31))
*/
{
    token->packed_fields = (token->packed_fields & 2147483647U) | ((((unsigned int)is_last) & 1U) << 31);
}
static const char *token_type_name(mu_json_token_type_t type) {
    if (type >= (sizeof(s_token_type_names) / sizeof(s_token_type_names[0]))) {
        return "MU_JSON_TOKEN_TYPE_UNKNOWN";
    } else {
        return s_token_type_names[type];
    }
}
static void log_input_state(const char *message, parser_t *p) {
}
static mu_json_token_t *find_sibling(mu_json_token_t *token,
                                     mu_json_token_t *(*m)(mu_json_token_t *)) {
    if (token_is_null(token) || token_is_first(token))
        return ((void *)0);
    mu_json_token_t *current = token;
    int target_level = ((int)((token->packed_fields >> 20) & 2047U));
    while (1) {
        current = m(current);
        if (token_is_null(current))
            return ((void *)0);
        if (((int)((current->packed_fields >> 20) & 2047U)) == target_level)
            return current;
        if (((int)((current->packed_fields >> 20) & 2047U)) < target_level)
            return ((void *)0);
    }
}
