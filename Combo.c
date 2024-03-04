#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdarg.h>
#include <stdlib.h>

int ShowSteps = 0, Extensional = 0, Statistics = 0; // Show steps, use extensionality, show statistics.

// Input format derived from the following syntax
// E = "(" E ")" | E E | X | "\" X+ ["."] E | X "=" E "," E.
// I've taken special measures to make this program completely non-recursive
// (even the tree traversals) and subject to the following conditions:
// (a) No expression is duplicated ... ever.
// (b) No reduction is duplicated ... ever.

// Scanner.
static int Line = 1, Errors = 0;
const int MaxErrors = 25;

static int Get(void) {
   int Ch = getchar();
   if (Ch == '\n') Line++;
   return Ch;
}

static void UnGet(int Ch) {
   if (Ch == '\n') --Line;
   ungetc(Ch, stdin);
}

static void Error(char *Format, ...) {
   fprintf(stderr, "[%d] ", Line);
   va_list AP; va_start(AP, Format); vfprintf(stderr, Format, AP); va_end(AP);
   fputc('\n', stderr);
   if (++Errors == MaxErrors) fprintf(stderr, "Reached the %d error limit.\n", MaxErrors), exit(1);
}

void *Allocate(unsigned Bytes) {
   void *X = malloc(Bytes); if (X == NULL) printf("Out of memory.\n"), exit(1);
   return X;
}

void *Reallocate(void *X, unsigned Bytes) {
   X = X == NULL? malloc(Bytes): realloc(X, Bytes); if (X == NULL) printf("Out of memory.\n"), exit(1);
   return X;
}

#define HASH_MAX 0x100
typedef unsigned char byte;
typedef struct Symbol *Symbol;
typedef struct Exp *Exp;
struct Symbol { char *Name; byte Hash; Exp E; Symbol Next, Tail; };
static Symbol HashTab[HASH_MAX], FirstB = NULL, LastB;

char *CopyS(char *S) {
   if (S == NULL) return NULL;
   char *NewS = Allocate(strlen(S) + 1);
   strcpy(NewS, S); return NewS;
}

byte Hash(char *S) {
   int H = 0;
   for (char *T = S; *T != '\0'; T++) H += *T;
   return H&0xff;
}

Symbol LookUp(char *S) {
   byte H = Hash(S);
   for (Symbol Sym = HashTab[H]; Sym != NULL; Sym = Sym->Next)
      if (strcmp(Sym->Name, S) == 0) return Sym;
   Symbol Sym = (Symbol)Allocate(sizeof *Sym);
   Sym->Name = CopyS(S); Sym->E = NULL;
   Sym->Hash = H, Sym->Next = HashTab[H], HashTab[H] = Sym;
   Sym->Tail = NULL;
   if (FirstB == NULL) FirstB = Sym; else LastB->Tail = Sym;
   return LastB = Sym;
}

// Used if Extensional is enabled.
Symbol Var(int New) {
   static char Name[12] = "#";
   static int Level = 0;
   sprintf(Name + 1, "%d", New? Level++: --Level);
   return LookUp(Name);
}

Symbol Sym;
char Scan(void) {
   static char CBuf[0x100];
   char Ch; char *CP;
   do Ch = Get(); while (isspace(Ch));
   switch (Ch) {
      case EOF: return '\0';
      case '(': case ')': case '=': case ',': case '.': case '\\': return Ch;
      default:
         if (!isalpha(Ch)) { Error("extra character %c", Ch); return '\0'; }
      case '_':
         for (CP = CBuf; isalnum(Ch) || Ch == '_'; CP++) {
            if (CP - CBuf >= sizeof CBuf) printf("Out of character space.\n"), exit(1);
            *CP = Ch, Ch = Get();
         }
         if (Ch != EOF) UnGet(Ch);
         if (CP - CBuf >= sizeof CBuf) printf("Out of character space.\n"), exit(1);
         *CP++ = '\0'; Sym = LookUp(CBuf);
      return 'x';
      case '"':
         Ch = Get();
         for (CP = CBuf; Ch != '"' && Ch != EOF; CP++) {
            if (CP - CBuf >= 0x100) printf("Out of character space.\n"), exit(1);
            *CP = Ch, Ch = Get();
         }
         if (Ch == EOF) printf("Missing closing \".\n"), exit(1);
         if (CP - CBuf >= sizeof CBuf) printf("Out of character space.\n"), exit(1);
         *CP++ = '\0'; Sym = LookUp(CBuf);
      return 'x';
   }
}

typedef Exp (*Task)(Exp E);
struct Exp {
   byte Leaf, Normal, State;
   int Arity, Hash; Exp Link, Ref, Next; Task Combo;
   union {
      Symbol X;
      struct { unsigned Mark, Visits; Exp Head, Tail; } App;
   } Body;
};
#define NN 0x200
static Exp ExpHash[NN];

// Tree automaton definitions.
// In a concurrent setting, (UN)SPIN waits on a lock, locks when Visits is initially 0,
// and unlocks when Visits is restored to 0.
// WriteExp() and Abstract() both use these macros.
#define SPIN(P, E, N) (\
   (N) = (E)->Body.App.Head, (E)->Body.App.Head = (E)->Body.App.Tail,\
   (E)->Body.App.Tail = (P), (E)->Body.App.Visits++\
)
#define UNSPIN(P, E, N) (\
   (P) = (E)->Body.App.Head, (E)->Body.App.Head = (E)->Body.App.Tail,\
   (E)->Body.App.Tail = (N), (E)->Body.App.Visits++\
)
#define DOWN(P, E, N) ((P) = (E), (E) = (N))
#define FLIP(P, E, N) ((N) = (P))

void WriteExp(Exp E) {
   Exp P, N; unsigned Write, Label;
// Pass 0: Find all the shared subexpressions.
   for (P = NULL; E != NULL; DOWN(P, E, N)) {
      if (E->Leaf) FLIP(P, E, N);
      else if (E->Body.App.Visits == 0 && E->Body.App.Mark)
         E->Body.App.Mark = 2, FLIP(P, E, N);
      else switch (SPIN(P, E, N)) {
         case 0: E->Body.App.Mark = 1; break;
         case 2: E->Body.App.Visits = 0; break;
      }
   }
// Pass 1: Label them and print out all the: _n = sub #n; from bottom up.
// Label = 3, 4, ... for _0, _1, ...
// Pass 2: Print out the rest of the expression.
// Write = 1 when in a subexpression for the second time.
// All subexpressions are scanned twice, and written out the second time.
   for (Write = 0; Write < 2; Write++)
   for (E = P, P = NULL, Label = 3; E != NULL; DOWN(P, E, N)) {
      if (E->Leaf) {
         if (Write) printf("%s", E->Body.X->Name);
         FLIP(P, E, N); continue;
      }
      if (E->Body.App.Visits == 0 && E->Body.App.Mark > 2) {
         if (Write) printf("_%u", E->Body.App.Mark - 3);
         FLIP(P, E, N); continue;
      }
      switch (SPIN(P, E, N)) {
         case 1:
            if (Write) {
               putchar(' ');
               if (!N->Leaf && N->Body.App.Mark <= 2) putchar('(');
            }
         break;
         case 2:
            E->Body.App.Visits = 0;
            if (Write) {
               if (!P->Leaf && P->Body.App.Mark < 2) putchar(')');
               if (E->Body.App.Mark == Label) Label++, printf(", "), Write = 0;
            } else if (E->Body.App.Mark == 2) {
               printf("_%u = ", Label - 3);
               E->Body.App.Mark = Label, Write = 1;
               UNSPIN(P, E, N), FLIP(P, E, N);
            }
         break;
      }
   }
// Pass 3: Clear out the marks.
   for (E = P, P = NULL; E != NULL; DOWN(P, E, N)) {
      if (E->Leaf) { FLIP(P, E, N); continue; }
      if (E->Body.App.Visits == 0 && E->Body.App.Mark == 0) { FLIP(P, E, N); continue; }
      switch (SPIN(P, E, N)) {
         case 0: E->Body.App.Mark = 0; break;
         case 2: E->Body.App.Visits = 0; break;
      }
   }
}

#define INFINITY 4
// Any value larger than all combinator arities will suffice.

Exp MakeSym(Symbol Sym) {
   if (Sym->E != NULL) return Sym->E;
   int H = (int)0x100 + Sym->Hash;
   for (Exp HP = ExpHash[H]; HP != NULL; HP = HP->Next)
      if (Sym == HP->Body.X) return HP;
   Exp E = (Exp)Allocate(sizeof *E);
   E->Body.X = Sym; E->Combo = NULL, E->Arity = INFINITY;
   E->Normal = 1, E->Link = E, E->State = 0;
   E->Ref = NULL, E->Hash = H; E->Leaf = 1;
   E->Next = ExpHash[H], ExpHash[H] = E;
   return E;
}

Exp Combinator(char *Name, Task Combo, int Arity) {
   static int Label = 0;
   Exp E = (Exp)Allocate(sizeof *E);
   E->Body.X = LookUp(Name); E->Body.X->E = E;
   E->Combo = Combo, E->Arity = Arity,
   E->Normal = 1, E->Link = E, E->State = 0;
   E->Ref = NULL, E->Hash = Label++; E->Leaf = 1;
   return E;
}

Exp Apply(Exp Head, Exp Tail) {
   if (Head == NULL || Tail == NULL) return NULL;
   while (Head->Link != NULL) {
      if (Head->Link == Head || Head->State > 0) break;
      Head = Head->Link;
   }
   while (Tail->Link != NULL) {
      if (Tail->Link == Tail || Tail->State > 0) break;
      Tail = Tail->Link;
   }
   int H = (Head->Hash + Tail->Hash)/4;
   for (Exp HP = ExpHash[H]; HP != NULL; HP = HP->Next)
      if (Head == HP->Body.App.Head && Tail == HP->Body.App.Tail) return HP;
   Exp E = (Exp)Allocate(sizeof *E);
   E->Body.App.Head = Head; E->Body.App.Tail = Tail;
   E->Body.App.Visits = 0; E->Body.App.Mark = 0;
   E->Combo = Head->Combo;
   E->Arity = !Head->Combo? INFINITY: Head->Arity < 0? -1: Head->Arity - 1;
   E->Normal = (!Extensional || Head->Arity == INFINITY || Tail->Arity == INFINITY) && E->Arity != 0 && Head->Normal && Tail->Normal;
   E->Link = E->Arity > 0? E: NULL;
   E->State = 0;
   E->Ref = NULL, E->Hash = H; E->Leaf = 0;
   E->Next = ExpHash[H], ExpHash[H] = E;
   return E;
}

unsigned Is, Ks, Ds, Ts, Ws, Us, Bs, Cs, Ss, Ns; // Used if Statistics is enabled.
unsigned Fs; // Used if Statistics is enabled with Extensional disabled.

Exp fI(Exp E) { // I u -> u
   if (Statistics) Is++; Ns++;
   return E->Body.App.Tail;
}
Exp fK(Exp E) { // K u v -> u
   if (Statistics) Ks++; Ns++;
   E = E->Body.App.Head;
   return E->Body.App.Tail;
}
Exp fD(Exp E) { // D u -> u u
   if (Statistics) Ds++; Ns++;
   Exp u = E->Body.App.Tail;
   return Apply(u, u);
}
Exp fT(Exp E) { // T u v -> v u
   if (Statistics) Ts++; Ns++;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(v, u);
}
Exp fW(Exp E) { // W u v -> u v v
   if (Statistics) Ws++; Ns++;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(Apply(u, v), v);
}
Exp fU(Exp E) { // U u v -> v (u v)
   if (Statistics) Us++; Ns++;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(v, Apply(u, v));
}
Exp fB(Exp E) { // B u v w -> u (v w)
   if (Statistics) Bs++; Ns++;
   Exp w = E->Body.App.Tail; E = E->Body.App.Head;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(u, Apply(v, w));
}
Exp fC(Exp E) { // C u v w -> u w v
   if (Statistics) Cs++; Ns++;
   Exp w = E->Body.App.Tail; E = E->Body.App.Head;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(Apply(u, w), v);
}
Exp fS(Exp E) { // S u v w -> u w (v w)
   if (Statistics) Ss++; Ns++;
   Exp w = E->Body.App.Tail; E = E->Body.App.Head;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(Apply(u, w), Apply(v, w));
}
// Used if Extensional is disabled.
Exp fF(Exp E) { // F u v w -> u v (v w)
   if (Statistics) Fs++; Ns++;
   Exp w = E->Body.App.Tail; E = E->Body.App.Head;
   Exp v = E->Body.App.Tail; E = E->Body.App.Head;
   Exp u = E->Body.App.Tail;
   return Apply(Apply(u, v), Apply(v, w));
}

Exp xI, xK, xD, xT, xW, xU, xB, xC, xS;
Exp xF; // Used if Extensional is disabled.
void InitSym(void) {
   xI = Combinator("I", fI, 1); xK = Combinator("K", fK, 2);
   xD = Combinator("D", fD, 1); xT = Combinator("T", fT, 2);
   xW = Combinator("W", fW, 2); xU = Combinator("U", fU, 2);
   xB = Combinator("B", fB, 3); xC = Combinator("C", fC, 3);
   xS = Combinator("S", fS, 3);
   if (!Extensional) xF = Combinator("F", fF, 3);
}

Exp Abstract(Exp E, Symbol X) { /* Calculate [E] = \x.E */
   Exp P, N, A, B;
   for (P = NULL; E != NULL; DOWN(P, E, N)) {
      if (E->Leaf) { // [x] = I, [A] = K A
         E->Ref = (E->Body.X == X)? NULL: E;
         FLIP(P, E, N); continue;
      }
      if (E->Ref != NULL) { FLIP(P, E, N); continue; }
      switch (SPIN(P, E, N)) {
         case 0: case 1: break;
         case 2:
            E->Body.App.Visits = 0;
            A = E->Body.App.Head->Ref; B = P->Ref;
            E->Ref =
               A == NULL?
                  B == NULL? xD: // [xx] = D
                  B == P? Apply(xT, B): // [xB] = T B
                  Apply(xU, B): // [xb] = U [b]
               A == E->Body.App.Head?
                  B == NULL? A: // [Ax] = A
                  B == P? E: // [AB] = K AB
                     Apply(Apply(xB, A), B): // [Ab] = B A[b]
                  B == NULL? Apply(xW, A): // [ax] = W [a]
                  B == P? Apply(Apply(xC, A), B): // [aB] = C [a] B
                     Apply(Apply(xS, A), B); // [ab] = S [a][b]
            if (Extensional && E->Normal) E->Ref->Normal = 1, E->Ref->Link = E->Ref;
         break;
      }
   }
   if (P == NULL) return NULL;
// P->Ref == NULL if P == x, P if [P] == K P, [P] otherwise.
   A = P->Ref == NULL? xI: P->Ref == P? Apply(xK, P): P->Ref;
   if (Extensional && P->Normal) A->Normal = 1, A->Link = A;
   for (E = P, P = NULL; E != NULL; DOWN(P, E, N)) { /* Clear out the Refs */
      if (E->Leaf) { E->Ref = NULL, FLIP(P, E, N); continue; }
      if (E->Ref == NULL) { FLIP(P, E, N); continue; }
      switch (SPIN(P, E, N)) {
         case 0: case 1: break;
         case 2: E->Ref = NULL; E->Body.App.Visits = 0; break;
      }
   }
   return A;
}

void Evaluate(Exp C) {
   if (Statistics) {
      if (!Extensional) Fs = 0;
      Ns = Is = Ks = Ds = Ts = Ws = Us = Bs = Cs = Ss = 0;
   }
   Exp D = NULL; int S = 2;
   if (C == NULL) goto Return;
   Exp E;
Start:
   if (C->State > 0) printf("Cyclic term: "), WriteExp(C), putchar('\n'), exit(1);
   if (C->Arity == 0 || C->Link != NULL && C->Link != C) {
      if (C->Link == NULL) {
         E = C->Combo(C);
         if (ShowSteps) {
            static int Steps = 0;
            WriteExp(C), printf(" => "), WriteExp(E), putchar('\n');
            if (++Steps >= 0x400) printf("Evaluation aborted: too many steps.\n"), exit(1);
         }
      } else E = C->Link;
      C->State = S, C->Link = D, D = C, C = E; goto Start;
   } else if (C->Arity > 0) {
      if (S == 1 || C->Normal) goto Normal;
      else if (!Extensional) {
         C->State = 4, C->Link = D, D = C, C = !C->Body.App.Head->Normal? C->Body.App.Head: C->Body.App.Tail; goto Start;
      } else if (C->Arity < INFINITY) {
         C->State = 5, C->Link = D, D = C, C = Apply(C, MakeSym(Var(1))); goto Start;
      } else if (!C->Body.App.Head->Normal) {
         C->State = 4, C->Link = D, D = C, C = C->Body.App.Head; goto Start;
      } else if (!C->Body.App.Tail->Normal) {
         C->State = 4, C->Link = D, D = C, C = C->Body.App.Tail; goto Start;
      } else {
         C->Normal = 1, C->Link = C; goto Normal;
      }
   } else {
      C->State = S + 2, C->Link = D, D = C, S = 1, C = C->Body.App.Head; goto Start;
   }
Normal:
   if (D == NULL) goto Return;
   else if (D->State <= 2) {
      E = D->Link, D->State = 0, D->Link = C, D = E;
      goto Normal;
   } else if (!Extensional || D->State <= 4) {
      S = D->State -= 2;
      C = Apply(D->Body.App.Head, D->Body.App.Tail);
      if (Extensional && C == D) D = C->Link, C->State = 0, C->Link = NULL;
      goto Start;
   } else if (Extensional) {
      E = D->Link, D->State = 0;
      C = Abstract(C, Var(0));
      D->Link = C, D = E; goto Normal;
   }
Return:
   WriteExp(C), putchar('\n');
   if (Statistics) {
      printf("steps: %d (I %d, K %d, D %d, T %d, W %d, U %d, B %d, C %d, S %d", Ns, Is, Ks, Ds, Ts, Ws, Us, Bs, Cs, Ss);
      if (!Extensional) printf(", F %d", Fs);
      printf(")\n");
   }
}

char *Stack; unsigned SX, SM;
Symbol *SStack; unsigned SSX, SSM;
Symbol *LStack; unsigned LSX, LSM;
Exp *EStack; unsigned ESX, ESM;
struct Frame { Symbol X; Exp E; } *FStack; unsigned FSX, FSM;
void Create(int Tag, ...) {
   va_list AP; va_start(AP, Tag);
   switch (Tag) {
      case '\0':
         SM = SX = 0, Stack = NULL;
         SSM = SSX = 0, SStack = NULL;
         ESM = ESX = 0, EStack = NULL;
         FSM = FSX = 0, FStack = NULL;
         LSM = LSX = 0, LStack = NULL;
      break;
      case '(': case '?': break;
      case ',':
         if (SSX >= SSM) SStack = Reallocate(SStack, sizeof *SStack*(SSM += 8));
         SStack[SSX++] = va_arg(AP, Symbol);
      break;
      case '=':
         if (FSX >= FSM) FStack = Reallocate(FStack, sizeof *FStack*(FSM += 8));
         FStack[FSX].X = va_arg(AP, Symbol), FStack[FSX].E = FStack[FSX].X->E, FStack[FSX++].X->E = va_arg(AP, Exp);
      break;
      case '\\':
         if (LSX >= LSM) LStack = Reallocate(LStack, sizeof *LStack*(LSM += 8));
         LStack[LSX++] = va_arg(AP, Symbol);
      break;
      case '.':
         if (ESX >= ESM) EStack = Reallocate(EStack, sizeof *EStack*(ESM += 8));
         EStack[ESX++] = va_arg(AP, Exp);
      break;
   }
   va_end(AP);
   if (SX >= SM) Stack = Reallocate(Stack, sizeof *Stack*(SM += 8));
   Stack[SX++] = Tag;
}

int Annihilate(char L) {
   int P;
   switch (L) {
      case 0: case ',': P = 0; break;
      case '=': P = 1; break;
      case ')': P = 2; break;
      case '.': P = 3; break;
      case '\\': case '(': case 'x': P = 4; break;
      default: P = 5; break;
   }
   int Top = Stack[--SX];
   switch (Top) {
      case 0:
         if (P < 1) {
            free(Stack), free(SStack), free(EStack), free(FStack), free(LStack);
            return Top;
         }
      break;
      case '?': if (P < 2) return Top; else break;
      case ',': if (P < 2) { SSX--; return Top; } else break;
      case '(': if (P < 3) return Top; else break;
      case '=':
         if (P < 4) {
            FSX--; FStack[FSX].X->E = FStack[FSX].E; return Top;
         }
      break;
      case '\\': if (P < 4) { LSX--; return Top; } else break;
      case '.': if (P < 5) { ESX--; return Top; } else break;
   }
   SX++; return -1;
}

void Usage(char *App) {
   fprintf(stderr, "Usage: %s [-s][-e][-x][-?][-h]\n", App);
   fprintf(stderr, "-s: Show steps, -e: Use the eta rule (extensionality), -x: Show statistics, -?/-h Print this message.\n");
}

int main(int AC, char *AV[]) {
   char *App = AC <= 0? NULL: AV[0]; if (App == NULL || *App == '\0') App = "Combo";
   int Status = 1;
   int DoU = 0;
   for (int A = 1; A < AC; ) {
      char *Arg = AV[A++];
      if (Arg[0] != '-') goto InvalidOption;
      char F = Arg[1];
      switch (F) {
         case 's': ShowSteps = 1; break;
         case 'e': Extensional = 1; break;
         case 'x': Statistics = 1; break;
         case '?': case 'h':
            if (!DoU) Usage(App), DoU = 1;
         break;
         default: InvalidOption: fprintf(stderr, "Unrecognized option: \"%s\".\n", Arg), Usage(App); goto Exit;
      }
   }
   Status = 0;
   if (DoU) goto Exit;
   Symbol X; Exp E, E1; int Act;
   InitSym();
   char L = Scan();
Parse:
   if (L == 0 || L == ',') goto Exit;
   Errors = 0;
   Create('\0');
ExpS:
   switch (L) {
      case ')': Error("Extra ')'."); L = Scan(); goto ExpS;
      case ',': case '.': L = Scan(); goto ExpS;
      case '(': Create('('); L = Scan(); goto ExpS;
      case '\\':
         L = Scan();
         if (L != 'x') { Error("Extra '\\'."); goto ExpS; }
         while (L == 'x') Create('\\', Sym), L = Scan();
         if (L == '.') L = Scan();
      goto ExpS;
      case 'x':
         X = Sym; L = Scan();
         if (L == '=') { Create(',', X); L = Scan(); goto ExpS; }
         E = MakeSym(X);
      goto ExpF;
      case '=':
         Error("Missing symbol in 'sym = E, E'.");
         Create('?'); L = Scan();
      goto ExpS;
      default: Error("Missing symbol."); E = NULL; goto ExpF;
   }
ExpF:
   switch (Act = Annihilate(L)) {
      case -1: goto ExpX;
      case 0:
         if (E == NULL)
            fprintf(stderr, "%d error(s)\n", Errors);
         else
            Evaluate(E);
      goto Parse;
      case '.': E = Apply(EStack[ESX], E); goto ExpF;
      case '\\': E = Abstract(E, LStack[LSX]); goto ExpF;
      case '=': goto ExpF;
      case '(':
         if (L != ')') Error("Missing ')'."); else L = Scan();
      goto ExpF;
      case '?': case ',':
         if (L != ',') Error("Missing ','."); else L = Scan();
         if (Act == ',') {
            if (E == NULL) Create('?'); else Create('=', SStack[SSX], E);
         }
      goto ExpS;
   }
ExpX:
   switch (L) {
      case '\\': case '(': case 'x': Create('.', E); goto ExpS;
      case '.': L = Scan(); goto ExpF;
      case ')': Error("Extra ')'."); L = Scan(); goto ExpF;
      case '=':
         Error("Expected symbol in 'sym = E, E'."); Create('?'); L = Scan();
      goto ExpS;
   }
Exit:
   return Status;
}
