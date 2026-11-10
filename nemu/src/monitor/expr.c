#include "nemu.h"
#include "cpu/reg.h"
#include "memory/memory.h"

#include <stdlib.h>

/* We use the POSIX regex functions to process regular expressions.
 * Type 'man regex' for more information about POSIX regex functions.
 */
#include <sys/types.h>
#include <regex.h>

enum
{
	NOTYPE = 256,
	EQ,
	NEQ,
	NUM,
	HEX,
	REG,
	SYMB,
	AND,
	OR,
	NOT,
	DEREF,
	NEG,
	PLUS = 43,
	MINUS = 45,
	STAR = 42,
	DIV = 47,
	LPAR = 40,
	RPAR = 41,

};

static struct rule
{
	char *regex;
	int token_type;
} rules[] = {

	{" +", NOTYPE}, // white space
	{"\\+", '+'},
	{"-", '-'},
	{"\\*", '*'},
	{"/", '/'},
	{"\\(", '('},
	{"\\)", ')'},
	{"==", EQ},
	{"!=", NEQ},
	{"&&", AND},
	{"\\|\\|", OR},
	{"!", NOT},
	{"\\$[a-z]+", REG},
	{"0x[0-9a-fA-F]+", HEX},
	{"[0-9]+", NUM},
	{"[a-zA-Z_][a-zA-Z0-9_]*", SYMB}
}
;

#define NR_REGEX (sizeof(rules) / sizeof(rules[0]))

static regex_t re[NR_REGEX];

/* Rules are used for more times.
 * Therefore we compile them only once before any usage.
 */
void init_regex()
{
	int i;
	char error_msg[128];
	int ret;

	for (i = 0; i < NR_REGEX; i++)
	{
		ret = regcomp(&re[i], rules[i].regex, REG_EXTENDED);
		if (ret != 0)
		{
			regerror(ret, &re[i], error_msg, 128);
			assert(ret != 0);
		}
	}
}

typedef struct token
{
	int type;
	char str[32];
} Token;

Token tokens[32];
int nr_token;

static bool make_token(char *e)
{
	int position = 0;
	int i;
	regmatch_t pmatch;

	nr_token = 0;

	while (e[position] != '\0')
	{
		/* Try all rules one by one. */
		for (i = 0; i < NR_REGEX; i++)
		{
			if (regexec(&re[i], e + position, 1, &pmatch, 0) == 0 && pmatch.rm_so == 0)
			{
				char *substr_start = e + position;
				int substr_len = pmatch.rm_eo;

				printf("match regex[%d] at position %d with len %d: %.*s\n", i, position, substr_len, substr_len, substr_start);
				position += substr_len;

				switch (rules[i].token_type)
				{
				case NOTYPE:
					break;
				default:
					if (nr_token >= (int)(sizeof(tokens) / sizeof(tokens[0])) ||
						substr_len >= (int)sizeof(tokens[0].str))
						return false;
					tokens[nr_token].type = rules[i].token_type;
					memcpy(tokens[nr_token].str, substr_start, substr_len);
					tokens[nr_token].str[substr_len] = '\0';
					nr_token++;
				}

				break;
			}
		}

		if (i == NR_REGEX)
		{
			printf("no match at position %d\n%s\n%*.s^\n", position, e, position, "");
			return false;
		}
	}

	return true;
}

static bool is_operand(int type)
{
	return type == NUM || type == HEX || 
	type == SYMB || type == REG || type == ')';
}

static int precedence(int type)
{
	switch (type)
	{
	case OR:
		return 1;
	case AND:
		return 2;
	case EQ:
	case NEQ:
		return 3;
	case PLUS:
	case MINUS:
		return 4;
	case STAR:
	case DIV:
		return 5;
	default:
		return 0;
	}
}

uint32_t look_up_symtab(char *sym, bool *success);

static bool check_parentheses(int p, int q)
{
	if (tokens[p].type != '(' || tokens[q].type != ')')
		return false;

	int depth = 0;
	for (int i = p; i <= q; i++)
	{
		if (tokens[i].type == '(')
			depth++;
		else if (tokens[i].type == ')')
		{
			depth--;
			if (depth == 0 && i != q)
				return false;
		}
	}
	return depth == 0;
}

static int dominant_operator(int p, int q, bool *ok)
{
	int op = -1;
	int depth = 0;

	for (int i = p; i <= q; i++)
	{
		int type = tokens[i].type;
		if (type == '(')
		{
			depth++;
			continue;
		}
		if (type == ')')
		{
			depth--;
			if (depth < 0)
			{
				*ok = false;
				return -1;
			}
			continue;
		}
		if (depth != 0)
			continue;

		int prec = precedence(type);
		if (prec != 0 && (op == -1 || prec <= precedence(tokens[op].type)))
			op = i;
	}

	if (depth != 0)
		*ok = false;
	return op;
}

static uint32_t eval(int p, int q, bool *ok)
{
	if (!*ok)
		return 0;

	if (p > q)
	{
		/* Bad expression */
		*ok = false;
		return 0;
	}

	if (p == q)
	{
		/* Single token */
		switch (tokens[p].type)
		{
		case NUM:
			return strtoul(tokens[p].str, NULL, 10);
		case HEX:
			return strtoul(tokens[p].str, NULL, 16);
		case REG:
		{
			bool found = true;
			uint32_t val = get_reg_val(tokens[p].str + 1, &found);
			if (!found)
				*ok = false;
			return val;
		}
		case SYMB:
			return look_up_symtab(tokens[p].str, ok);
		default:
			*ok = false;
			return 0;
		}
	}

	if (check_parentheses(p, q))
		return eval(p + 1, q - 1, ok);

	int op = dominant_operator(p, q, ok);
	if (!*ok)
		return 0;

	if (op == -1)
	{
		switch (tokens[p].type)
		{
		case NEG:
			return (uint32_t)(-(int32_t)eval(p + 1, q, ok));
		case NOT:
			return !eval(p + 1, q, ok);
		case DEREF:
			return vaddr_read(eval(p + 1, q, ok), SREG_DS, 4);
		default:
			*ok = false;
			return 0;
		}
	}

	uint32_t val1 = eval(p, op - 1, ok);
	uint32_t val2 = eval(op + 1, q, ok);
	if (!*ok)
		return 0;

	switch (tokens[op].type)
	{
	case PLUS:
		return val1 + val2;
	case MINUS:
		return val1 - val2;
	case STAR:
		return val1 * val2;
	case DIV:
		if (val2 == 0)
		{
			*ok = false;
			return 0;
		}
		return val1 / val2;
	case EQ:
		return val1 == val2;
	case NEQ:
		return val1 != val2;
	case AND:
		return val1 && val2;
	case OR:
		return val1 || val2;
	default:
		*ok = false;
		return 0;
	}
}

uint32_t expr(char *e, bool *success)
{
	if (!make_token(e))
	{
		*success = false;
		return 0;
	}
	
	for (int i = 0; i < nr_token; i++)
	{
		bool unary_pos = (i == 0) || !is_operand(tokens[i - 1].type);
		if (unary_pos && tokens[i].type == STAR)
			tokens[i].type = DEREF;
		else if (unary_pos && tokens[i].type == MINUS)
			tokens[i].type = NEG;
	}

	bool ok = true;
	uint32_t val = eval(0, nr_token - 1, &ok);
	*success = ok;
	return val;
}
