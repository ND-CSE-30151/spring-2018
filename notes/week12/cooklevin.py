from tock import *
import itertools

def transitions(m):
    """Convert from Tock's internal format to tuples (q, a, r, b, d), where
    - q is the current state
    - a is the symbol read
    - r is the new state
    - b is the symbol written
    - d (-1 or 1) is the direction moved
    """
    tuples = []
    for t in m.get_transitions():
        (q,), (a,) = t.lhs
        (r,), bstore = t.rhs
        tuples.append((q, a, r, bstore[0], bstore.position))
    return tuples

def tape_alphabet(m):
    """Return the tape alphabet (Gamma) of m."""
    gamma = {syntax.BLANK}
    for _, a, _, b, _ in transitions(m):
        gamma.add(a)
        gamma.add(b)
    return gamma

class Formula(object):
    def __init__(self, op, args):
        self.op = op
        self.args = args
    def __str__(self):
        if self.op == "var":
            return self.args[0]
        elif self.op == '~':
            x, = self.args
            if x.op in ['&', '|']:
                x = "({})".format(x)
            return "~{}".format(x)
        elif self.op == '&':
            arg_strs = []
            for arg in self.args:
                if arg.op == '|':
                    arg_strs.append("({})".format(arg))
                else:
                    arg_strs.append(str(arg))
            return " & ".join(arg_strs)
        elif self.op == '|':
            return " | ".join(map(str, self.args))
        else:
            raise ValueError()
    def pretty_print(self):
        limit = 5
        if self.op == "var":
            return self.args[0]
        elif self.op == '~':
            x, = self.args
            if x.op in ['&', '|']:
                x = "({})".format(x.pretty_print())
            else:
                x = x.pretty_print()
            return "~{}".format(x)
        elif self.op == '&':
            arg_strs = []
            for arg in self.args[:limit]:
                if arg.op == '|':
                    arg_strs.append("({})".format(arg.pretty_print()))
                else:
                    arg_strs.append(arg.pretty_print())
            if len(self.args) > limit:
                arg_strs.append("...")
            return " & ".join(arg_strs)
        elif self.op == '|':
            arg_strs = [arg.pretty_print() for arg in self.args[:limit]]
            if len(self.args) > limit:
                arg_strs.append("...")
            return " | ".join(arg_strs)
        else:
            raise ValueError()

    def __and__(self, other):
        return make_and(self, other)
    def __rand__(self, other):
        return make_and(other, self)
    def __or__(self, other):
        return make_or(self, other)
    def __ror__(self, other):
        return make_or(other, self)
    def __invert__(self):
        return make_not(self)

def make_or(*args):
    new_args = []
    for arg in args:
        if arg == True: return True
        elif arg == False: continue
        elif arg.op == '|': new_args.extend(arg.args)
        else: new_args.append(arg)
    return Formula("|", new_args)
def make_and(*args):
    new_args = []
    for arg in args:
        if arg == True: continue
        elif arg == False: return False
        elif arg.op == '&': new_args.extend(arg.args)
        else: new_args.append(arg)
    return Formula("&", new_args)
def make_not(x):
    if x in [False, True]: return not x
    return Formula("~", [x])
def make_var(x):
    return Formula("var", [x])

def make_phi(m, w, k):
    """Convert the run of NTM m on input w to a Boolean formula 
    that is satisfiable iff m accepts w in at most |w|**k steps."""
    n = len(w)
    nk = max(n**k, n+3)
    gamma = tape_alphabet(m)
    C = gamma | m.states | {"#"}
    q0 = m.get_start_state()
    [qf] = m.get_accept_states()
    x = {}
    for i in range(1,nk+1):
        for j in range(1,nk+1):
            for s in C:
                x[i,j,s] = make_var("x[{},{},{}]".format(i,j,s))

    phi_cell = True

    # For each cell,
    for i in range(1,nk+1):
        for j in range(1,nk+1):
            
            # the cell must have a value
            at_least_one = False
            for s in C:
                at_least_one |= x[i,j,s]

            # and the cell must have at most one value
            at_most_one = True
            for s in C:
                for t in C:
                    if s != t:
                        at_most_one &= ~x[i,j,s] | ~x[i,j,t]

            phi_cell &= at_least_one & at_most_one

    # The first row should be the initial configuration
    phi_start = True
    phi_start &= x[1,1,"#"]                 # endmarker
    phi_start &= x[1,2,m.get_start_state()] # head
    for i in range(n):
        phi_start &= x[1,i+3,w[i]]          # input symbols
    for i in range(n+3,nk):
        phi_start &= x[1,i,syntax.BLANK]    # blank symbols
    phi_start &= x[1,nk,"#"]                # endmarker

    # Each row should be a legal successor configuration of the row above it
    phi_move = True

    # For each 2x3 window,
    for i in range(1,nk):
        for j in range(1,nk-1):

            phi_legal = False

            for t1 in gamma | {"#"}:
                for t2 in gamma:
                    for t3 in gamma | {"#"}:
                        phi_legal |= (x[i,j,  t1] & x[i,j+1,  t2] & x[i,j+2,  t3] &
                                      x[i+1,j,t1] & x[i+1,j+1,t2] & x[i+1,j+2,t3])

            for q, b, r, c, d in transitions(m):
                if d == -1: # move left: uaqbv becomes uracv
                    for u1 in gamma | {"#"}:
                        for u2 in gamma:
                            for a in gamma:
                                phi_legal |= (x[i,j,  u1] & x[i,j+1,  u2] & x[i,j+2,  a] &
                                              x[i+1,j,u1] & x[i+1,j+1,u2] & x[i+1,j+2,r])

                    for u2 in gamma | {"#"}:
                        for a in gamma:
                            phi_legal |= (x[i,j,  u2] & x[i,j+1,  a] & x[i,j+2,  q] &
                                          x[i+1,j,u2] & x[i+1,j+1,r] & x[i+1,j+2,a])

                    for a in gamma:
                        phi_legal |= (x[i,j,  a] & x[i,j+1,  q] & x[i,j+2,  b] &
                                      x[i+1,j,r] & x[i+1,j+1,a] & x[i+1,j+2,c])
                    # special case: if head is at left end, it does not move
                    phi_legal |= (x[i,j,  "#"] & x[i,j+1,  q] & x[i,j+2,  b] &
                                  x[i+1,j,"#"] & x[i+1,j+1,r] & x[i+1,j+2,c])

                    for a in gamma:
                        for v1 in gamma | {"#"}:
                            phi_legal |= (x[i,j,  q] & x[i,j+1,  b] & x[i,j+2,  v1] &
                                          x[i+1,j,r] & x[i+1,j+1,a] & x[i+1,j+2,v1])

                    for a in gamma:
                        for v1 in gamma:
                            for v2 in gamma | {"#"}:
                                phi_legal |= (x[i,j,  b] & x[i,j+1,  v1] & x[i,j+2,  v2] &
                                              x[i+1,j,a] & x[i+1,j+1,v1] & x[i+1,j+2,v2])

                elif d == +1: # move right: uaqbv becomes uacrv
                    for a in gamma:
                        for u in gamma | {"#"}:
                            phi_legal |= (x[i,j,  u] & x[i,j+1,  q] & x[i,j+2,  q] &
                                          x[i+1,j,u] & x[i+1,j+1,a] & x[i+1,j+2,c])

                    for a in gamma | {"#"}:
                        phi_legal |= (x[i,j,  a] & x[i,j+1,  q] & x[i,j+2,  b] &
                                      x[i+1,j,a] & x[i+1,j+1,c] & x[i+1,j+2,r])

                    for v1 in gamma:
                        phi_legal |= (x[i,j,  q] & x[i,j+1,  b] & x[i,j+2,  v1] &
                                      x[i+1,j,c] & x[i+1,j+1,r] & x[i+1,j+2,v1])

                    for v1 in gamma:
                        for v2 in gamma | {"#"}:
                            phi_legal |= (x[i,j,  b] & x[i,j+1,  v1] & x[i,j+2,  v2] &
                                          x[i+1,j,r] & x[i+1,j+1,v1] & x[i+1,j+2,v2])

                else:
                    raise ValueError("invalid direction")
            
            phi_move &= phi_legal

    # The accept state should occur somewhere
    phi_accept = False
    for i in range(1,nk+1):
        for j in range(1,nk+1):
            phi_accept |= x[i,j,qf]

    return phi_cell & phi_start & phi_move & phi_accept
