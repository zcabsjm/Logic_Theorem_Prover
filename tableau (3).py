MAX_CONSTANTS = 10
prop_letters = ["p", "q", "r", "s"]
binary_connectives = ["=", "^", "v", ">"]
negation = ["-"]
variables = ["x", "y", "z", "w"]
predicates = ["P", "Q", "R", "S"]
quantifiers = ["E", "A"]
available_constants = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]



def is_firstorderlogic(fmla):
    for char in fmla:
        if char in variables or char in predicates:
            return True
    return False



def is_negation(fmla):
    if len(fmla) == 1:
        return 0
    ans = parse(fmla[1:])
    if fmla[0] == "-" and ans:
        if ans in [1, 2, 3, 4, 5]:
            return 2
        elif ans in [6, 7, 8]:
            return 7
    return 0

def find_binary_connective(fmla):
    indexes = []
    for i in range(len(fmla)):
        if fmla[i] in binary_connectives:
            indexes.append(i)
    return indexes









# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    if fmla is None:
        return 0
    if len(fmla) == 1 and fmla in prop_letters:
        return 6
    if fmla[0] in predicates and fmla[1] == ("(") and fmla[-1] == (")"):
        first = fmla[2]
        com = fmla[3]
        second = fmla[4]
        if first in variables + available_constants and second in variables + available_constants and com == ",":
            return 1
    is_neg = is_negation(fmla)
    if is_neg:
        return is_neg
    if parse(lhs(fmla)) in [1, 2, 3, 4, 5] and parse(rhs(fmla)) in [1, 2, 3, 4, 5]:
        return 5
    elif parse(lhs(fmla)) in [6, 7, 8] and parse(rhs(fmla)) in [6, 7, 8]:
        return 8
    if fmla[0] == quantifiers[0] and fmla[1] in variables and parse(fmla[2:]):
        return 4
    if fmla[0] == quantifiers[1] and fmla[1] in variables and parse(fmla[2:]):
        return 3
    return 0

# Return the LHS of a binary connective formula
def lhs(fmla):
    if fmla[0] == "(" and fmla[-1] == ")":
        fmla = fmla[1:-1]
    for i in find_binary_connective(fmla):
        if parse(fmla[0:i]) and parse(fmla[i + 1:]):
            return fmla[0:i]

# Return the connective symbol of a binary connective formula
def con(fmla):
    if fmla[0] == "(" and fmla[-1] == ")":
        fmla = fmla[1:-1]
    for i in find_binary_connective(fmla):
        if parse(fmla[0:i]) and parse(fmla[i + 1:]):
            return fmla[i]
    return 0

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    if fmla[0] == "(" and fmla[-1] == ")":
        fmla = fmla[1:-1]
    for i in find_binary_connective(fmla):
        if parse(fmla[0:i]) and parse(fmla[i + 1:]):
            return fmla[i+1:]



# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    theory = []
    theory.append([fmla])
    return theory

#check for satisfiability
def sat(tableau):
    constants = list(available_constants)
    while len(tableau) != 0:
        theory = tableau.pop(0)
        if Exp(theory) and not Contradictory(theory):
            return 1
        else:
            for fmla in theory:
                if alpha_fmla_type1(fmla):
                    fmla1 = lhs(fmla)
                    fmla2 = rhs(fmla)
                    theory.remove(fmla)
                    theory.append(fmla1)
                    theory.append(fmla2)
                    if not Contradictory(theory):
                        tableau.append(theory)
                if alpha_fmla_type2(fmla):
                    theory.remove(fmla)
                    fmla = fmla[2:]
                    theory.append(fmla)
                    if not Contradictory(theory):
                        tableau.append(theory)

                if alpha_fmla_type3(fmla):
                    fmla = fmla[1:]
                    fmla1 = "-" + lhs(fmla)
                    fmla2 = "-" + rhs(fmla)
                    theory.remove(fmla)
                    theory.append(fmla1)
                    theory.append(fmla2)
                    break
                    if not Contradictory(theory):
                        tableau.append(theory)


                if alpha_fmla_type4(fmla):
                    fmla = fmla[1:]
                    fmla1 = lhs(fmla)
                    fmla2 = "-" + rhs(fmla)
                    theory.remove(fmla)
                    theory.append(fmla1).apppend(fmla2)
                    break
                    if not Contradictory(theory):
                        tableau.append(theory)

                if beta_fmla_type1(fmla):
                    theory.remove(fmla)
                    theory1 = list(theory) # () used to make copy of list
                    theory2 = list(theory)
                    fmla1 = lhs(fmla)
                    fmla2 = rhs(fmla)
                    theory1.append(fmla1)
                    if not Contradictory(theory1) and theory1 not in tableau:
                        tableau.append(theory1)
                    theory2.append(fmla2)
                    if not Contradictory(theory2) and theory2 not in tableau:
                        tableau.append(theory2)
                    break

                if beta_fmla_type2(fmla):
                    theory.remove(fmla)
                    theory1 = list(theory)
                    theory2 = list(theory)
                    fmla1 = "-" + lhs(fmla[1:])
                    fmla2 = "-" + rhs(fmla[1:])
                    theory1.append(fmla1)
                    if not Contradictory(theory1):
                        tableau.append(theory1)
                    theory2.append(fmla2)
                    if not Contradictory(theory2):
                        tableau.append(theory2)
                    break

                if beta_fmla_type3(fmla):
                    theory.remove(fmla)
                    theory1 = list(theory)
                    theory2 = list(theory)
                    fmla1 = "-" + lhs(fmla)
                    fmla2 = rhs(fmla)
                    theory1.append(fmla1)
                    break
                    if not Contradictory(theory1):
                        tableau.append(theory1)
                    theory2.append(fmla2)
                    if not Contradictory(theory2):
                        tableau.append(theory2)
                    break

                if delta_fmla_1(fmla):
                    fmla1 = fmla[1:]
                    fmla2 = replace(fmla1[1:], fmla1[0], constants[0])
                    constants.pop(0)
                    theory.remove(fmla)
                    theory.append(fmla2)
                    if not Contradictory(theory):
                        tableau.append(theory)
                    break

                if delta_fmla_2(fmla):
                    fmla1 = fmla[2:]
                    fmla2 = "-" + replace(fmla1[1:], fmla1[0], constants[0])
                    constants.pop(0)
                    theory.remove(fmla)
                    theory.append(fmla2)
                    if not Contradictory(theory):
                        tableau.append(theory)
                    break

                if gamma_fmla_1(fmla):
                    fmla1 = fmla[1:]
                    theory.remove(fmla)
                    for constant in available_constants:
                        fmla2 = replace(fmla1[1:], fmla1[0], constant)
                        theory1 = list(theory)
                        theory1.append(fmla2)
                        if not Contradictory(theory1):
                            tableau.append(theory1)
                    break

                if gamme_fmla_2(fmla):
                    fmla1 = fmla[2:]
                    theory.remove(fmla)
                    for constant in available_constants:
                        fmla2 = "-" + replace(fmla1[1:], fmla1[0], constant)
                        theory1 = list(theory)
                        theory1.append(fmla2)
                        if not Contradictory(theory1):
                            tableau.append(theory1)
                    break

#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    return 0

def Contradictory(theory):
    for fmla1 in theory:
        for fmla2 in theory:
            if "-" + fmla1 == fmla2:
                return True
    return False

def Exp(theory):
    for fmla1 in theory:
        if parse(fmla1) in [2, 7]:
            if not Exp([fmla1[1:]]):
                return False
        elif parse(fmla1) not in [1, 6]:
            return False
    return True

def alpha_fmla_type1(fmla): # ^
    if con(fmla) == ("^"):
        return True
    return False

def alpha_fmla_type2(fmla): # --
    if len(fmla) > 2 and fmla[0] == ("-") and fmla[1] == ("-"):
        return True
    return False

def alpha_fmla_type3(fmla): # -(pVq)
    if parse(fmla) == [2, 7]:
        fmla = fmla[1:]
        if con(fmla) == ("v"):
            return True
    return False

def alpha_fmla_type4(fmla):
    if parse(fmla) == [2, 7]:
        fmla = fmla[1:]
        if con(fmla) == (">"):
            return True
    return False

def beta_fmla_type1(fmla):
    if con(fmla) == ("v"):
        return True
    return False

def beta_fmla_type2(fmla):
    if parse(fmla) in [2, 7]:
        if con(fmla[1:]) == ("^"):
            return True
    return False

def beta_fmla_type3(fmla):
    if con(fmla) == (">"):
        return True
    return False

def delta_fmla_1(fmla):
    if parse(fmla) == 4:
        return True
    return False

def delta_fmla_2(fmla):
    if fmla[0] == "-" and fmla[1] == "A":
        return True
    return False

def gamma_fmla_1(fmla):
    if fmla[0] == "A":
        return True
    return False

def gamme_fmla_2(fmla):
    if fmla[0] == "-" and fmla[1] == "E":
        return True
    return False


def replace(fmla, variable, constant):
    result = parse(fmla)
    if result in [0, 6, 7, 8]:
        return fmla
    elif result in [3, 4]:
        if fmla[1] == variable:
            return fmla
        return fmla[:2] + replace(fmla[2:], variable, constant)
    elif result in [2]:
        return fmla[:1] + replace(fmla[1:], variable, constant)
    elif result in [5]:
        fmla1 = lhs(fmla)
        fmla2 = rhs(fmla)
        result = "(" + replace(fmla1, variable, constant) + con(fmla) + replace(fmla2, variable, constant) + ")"
        return result
    elif result in [1]:
        return fmla.replace(variable, constant)

#DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()


PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)

