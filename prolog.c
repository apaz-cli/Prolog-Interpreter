/* Adapted from https://www.cl.cam.ac.uk/~am21/research/funnel/prolog.c */
/* prolog.c: a simple Prolog interpreter written in C++,                */
/*           including an example test run as main().                   */
/* Copyright (c) Alan Mycroft, University of Cambridge, 2000.           */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Misc helpers */

static inline void *prover_malloc(size_t n) {
  void *ptr = malloc(n);
  if (!ptr)
    puts("\nOut of Memory.\n");
  return ptr;
}

static inline void indent(size_t indents, const size_t size) {
  for (size_t i = 0; i < (indents * size); i++)
    putchar(' ');
}

typedef struct {
  size_t t1;
  size_t t2;
} Timestamp;
static Timestamp timestamp = {.t1 = 0, .t2 = 0};
static inline Timestamp timestamp_next() {
  if ((timestamp.t1 += 1) == 0)
    timestamp.t2 += 1;
  return timestamp;
}

static inline bool timestamp_cmp(Timestamp ts1, Timestamp ts2) {
  if (ts1.t2 > ts2.t2)
    return true;
  if (ts1.t1 > ts2.t1)
    return true;
  return false;
}

/****************/
/* Declarations */
/****************/

typedef char *Atom;
union Term;
typedef union Term Term;
struct Trail;
typedef struct Trail Trail;
struct Goal;
typedef struct Goal Goal;
struct Clause;
typedef struct Clause Clause;
struct Program;
typedef struct Program Program;

/****************/
/* Term Structs */
/****************/

typedef struct {
  size_t arity;
  Atom fsym;
  Term **subterms;
} TermConstant;

typedef struct {
  Term *instance;
  Timestamp timestamp;
} TermVariable;

typedef struct Term {
  union {
    TermVariable tv; // tc_flag = 0
    TermConstant tc; // tc_flag = 1
  };
  bool tc_flag;
} Term;

static inline bool Term_isCons(Term* term) { return term->tc_flag == 1; }
static inline bool Term_isVar(Term* term)  { return term->tc_flag == 0; }


/************/
/* TermCons */
/************/

/* Shares ownership of subterms */
static inline Term *TermCons_init(Term *self, Atom f, Term** subterms, size_t arity) {
  self->tc.fsym = f;
  self->tc.subterms = subterms;
  self->tc.arity = arity;
  self->tc_flag = true;
  return self;
}

#define _PROLOG_TERMBUF(n)  Term** buf = prover_malloc(sizeof(Term*) * n);

static inline Term *TermCons_init0(Term *self, Atom f) {
  return TermCons_init(self, f, NULL, 0);
}

static inline Term *TermCons_init1(Term *self, Atom f, Term* term1) {
  _PROLOG_TERMBUF(1);
  buf[0] = term1;
  return TermCons_init(self, f, buf, 1);
}
static inline Term *TermCons_init2(Term *self, Atom f, Term* term1, Term* term2) {
  _PROLOG_TERMBUF(2);
  buf[0] = term1;
  buf[1] = term2;
  return TermCons_init(self, f, buf, 2);
}
static inline Term *TermCons_init3(Term *self, Atom f, Term* term1, Term* term2, Term* term3) {
  _PROLOG_TERMBUF(3);
  buf[0] = term1;
  buf[1] = term2;
  buf[2] = term3;
  return TermCons_init(self, f, buf, 3);
}
static inline Term *TermCons_init4(Term *self, Atom f, Term* term1, Term* term2, Term* term3, Term* term4) {
  _PROLOG_TERMBUF(4);
  buf[0] = term1;
  buf[1] = term2;
  buf[2] = term3;
  buf[3] = term4;
  return TermCons_init(self, f, buf, 4);
}

/***********/
/* TermVar */
/***********/


static inline Term *TermVar_init(Term *self) {
  self->tc_flag = false;
  self->tv.instance = self;
  self->tv.timestamp = timestamp_next();
  return self;
}

/*******************************/
/* Term (Shared Functionality) */
/*******************************/

static inline void Term_print(Term *self) {}

static inline bool Term_unify(Term *self, Term *other) {
  /* Both TermCons */
  if (Term_isCons(self) & Term_isCons(other)) {
    if (self->tc.arity != other->tc.arity) return false;
    if (!Atom_eq(self->tc.fsym, other->tc.fsym)) return false;
    size_t arity = self->tc.arity;
    for (size_t i = 0; i < arity; i++)
      if (!Term_unify(self->tc.subterms[i], other->tc.subterms[i]))
        return false;
    return true;
  }
  /* Both TermVar */
  else if (Term_isVar(self) & Term_isVar(other)) {
  }
  /* Mixed */
  else {
    Term* cons = Term_isCons(self) ? self : other;
    Term* var  = Term_isVar(self)  ? self : other;
  }
}

static inline Term* Term_copy(Term *self) {
  if (Term_isCons(self)) {
    size_t arity = self->tc.arity;
    char *buf = prover_malloc(sizeof(Term) + sizeof(Term) * arity);
    Term *cpy = (Term *)buf;
    Term *subterms = cpy + 1;
    memcpy(subterms, self->tc.subterms, self->tc.arity);
    return TermCons_init(cpy, self->tc.fsym, subterms, arity);
  } else {
    return TermVar_init((Term *)prover_malloc(sizeof(Term)));
  }
}

/*********/
/* Trail */
/*********/

typedef struct {
  /* A TermVar */
  Term* var;
  /* Linked List */
  Trail* prev;
} Trail;

static Trail* sofar = NULL;

static inline Trail* Trail_init(Trail* self, Term* var, Trail* prev) {
  self->var = var;
  self->prev = prev;
  return self;
}

static inline Trail* Trail_note() { return sofar; }
static inline void Trail_push(TermVar *x) { sofar = new Trail(x, sofar); }
static void Trail_backtrack(Trail* to) {
  for (; sofar != to; sofar = sofar->prev)
    sofar->tcar->reset();
  }
}


/********/
/* Goal */
/********/

/**********/
/* Clause */
/**********/

/***********/
/* Program */
/***********/


class TermCons : public Term {
private:
  int arity;
  Atom *fsym;
  Term **args;

public:
  bool unify(Term *t) { return t->unify2(this); }

private:
  TermCons(TermCons *p)
      : fsym(p->fsym), arity(p->arity),
        args(p->arity == 0 ? NULL : new Term *[p->arity]) {
    for (int i = 0; i < arity; i++)
      args[i] = p->args[i]->copy();
  }
  bool unify2(TermCons *t) {
    if (!(fsym->eqatom(t->fsym) && arity == t->arity))
      return false;
    for (int i = 0; i < arity; i++)
      if (!args[i]->unify(t->args[i]))
        return false;
    return true;
  }
};

class TermVar : public Term {
private:
  Term *instance;
  int varno;
  static int timestamp;

public:
  TermVar() : instance(this), varno(++timestamp) {}
  void print() {
    if (instance != this)
      instance->print();
    else
      cout << "_" << varno;
  };
  bool unify(Term *t);
  Term *copy();
  Term *reset() { instance = this; }

private:
  bool unify2(TermCons *t) { return this->unify(t); }
};

class Program;
class TermVarMapping;

class Goal {
private:
  TermCons *car;
  Goal *cdr;

public:
  Goal(TermCons *h, Goal *t) : car(h), cdr(t) {}
  Goal *copy() {
    return new Goal(car->copy2(), cdr == NULL ? NULL : cdr->copy());
  }
  Goal *append(Goal *l) {
    return new Goal(car, cdr == NULL ? NULL : cdr->append(l));
  }
  void print() {
    car->print();
    if (cdr != NULL) {
      cout << "; ", cdr->print();
    }
  }
  void solve(Program *p, int level, TermVarMapping *map);
};

class Clause {
public:
  TermCons *head;
  Goal *body;
  Clause(TermCons *h, Goal *t) : head(h), body(t) {}
  Clause *copy() {
    return new Clause(head->copy2(), body == NULL ? NULL : body->copy());
  }
  void print() {
    head->print();
    cout << " :- ";
    if (body == NULL)
      cout << "true";
    else
      body->print();
  }
};

class Program {
public:
  Clause *pcar;
  Program *pcdr;
  Program(Clause *h, Program *t) : pcar(h), pcdr(t) {}
};

class Trail {
private:
  TermVar *tcar;
  Trail *tcdr;
  static Trail *sofar;
  Trail(TermVar *h, Trail *t) : tcar(h), tcdr(t) {}

public:
  static Trail *Note() { return sofar; }
  static void Push(TermVar *x) { sofar = new Trail(x, sofar); }
  static void Undo(Trail *whereto) {
    for (; sofar != whereto; sofar = sofar->tcdr)
      sofar->tcar->reset();
  }
};
Trail *Trail::sofar = NULL;

bool TermVar::unify(Term *t) {
  if (instance != this)
    return instance->unify(t);
  Trail::Push(this);
  instance = t;
  return true;
}
Term *TermVar::copy() {
  if (instance == this) {
    Trail::Push(this);
    instance = new TermVar();
  }
  return instance;
}

class TermVarMapping {
private:
  TermVar **varvar;
  char **vartext;
  int size;

public:
  TermVarMapping(TermVar *vv[], char *vt[], int vs)
      : varvar(vv), vartext(vt), size(vs) {}
  void showanswer() {
    if (size == 0)
      cout << "yes\n";
    else {
      for (int i = 0; i < size; i++) {
        cout << vartext[i] << " = ";
        varvar[i]->print();
        cout << "\n";
      }
    }
  }
};

void Goal::solve(Program *p, int level, TermVarMapping *map) {
  indent(level .4);
  cout << "solve@" << level << ": ";
  this->print();
  cout << "\n";
  for (Program *q = p; q != NULL; q = q->pcdr) {
    Trail *t = Trail::Note();
    Clause *c = q->pcar->copy();
    Trail::Undo(t);
    indent(level, 4);
    cout << "  try:";
    c->print();
    cout << "\n";
    if (car->unify(c->head)) {
      Goal *gdash = c->body == NULL ? cdr : c->body->append(cdr);
      if (gdash == NULL)
        map->showanswer();
      else
        gdash->solve(p, level + 1, map);
    } else {
      indent(level, 4);
      cout << "  nomatch.\n";
    }
    Trail::Undo(t);
  }
}

/* A sample test program: append */

Atom *at_app = new Atom("app");
Atom *at_cons = new Atom("cons");
TermConstant *f_nil = new TermCons(new Atom("nil"));
TermConstant *f_1 = new TermCons(new Atom("1"));
TermConstant *f_2 = new TermCons(new Atom("2"));
TermConstant *f_3 = new TermCons(new Atom("3"));

Term *v_x = new TermVar();
TermConstant *lhs1 = new TermCons(at_app, f_nil, v_x, v_x);
Clause *c1 = new Clause(lhs1, NULL);

Term *v_l = new TermVar();
Term *v_m = new TermVar();
Term *v_n = new TermVar();
TermConstant *rhs2 = new TermCons(at_app, v_l, v_m, v_n);
TermConstant *lhs2 = new TermCons(at_app, new TermCons(at_cons, v_x, v_l), v_m,
                                  new TermCons(at_cons, v_x, v_n));
Clause *c2 = new Clause(lhs2, new Goal(rhs2, NULL));

TermVariable *v_i = new TermVar();
TermVariable *v_j = new TermVar();
TermConstant *rhs3 =
    new TermCons(at_app, v_i, v_j,
                 new TermCons(at_cons, f_1,
                              new TermCons(at_cons, f_2,
                                           new TermCons(at_cons, f_3, f_nil))));

Goal *g1 = new Goal(rhs3, NULL);

Program *test_p = new Program(c1, new Program(c2, NULL));
Program *test_p2 = new Program(c2, new Program(c1, NULL));

TermVariable *varvar[] = {v_i, v_j};
char *varname[] = {"I", "J"};
TermVarMapping *var_name_map = new TermVarMapping(varvar, varname, 2);

int main(int argc, char *argv[]) {
  cout << "=======Append with normal clause order:\n";
  g1->solve(test_p, 0, var_name_map);
  cout << "\n=======Append with reversed normal clause order:\n";
  g1->solve(test_p2, 0, var_name_map);
  return 0;
}
