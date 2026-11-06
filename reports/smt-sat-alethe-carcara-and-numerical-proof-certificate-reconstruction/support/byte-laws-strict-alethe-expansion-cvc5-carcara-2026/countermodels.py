"""Owned finite model evaluator and literal Lean witness producer.

Only this fixture's reported scalar/select values and syntax are supported;
unknown operators/values fail, never default. This is not an SMT model checker.
"""
from translate import parse_terms


ARRAYS = ['source', 'current', 'source_init', 'source_read', 'current_init',
          'current_read', 'write_authority']


def atom(term):
    if term == 'true':
        return True
    if term == 'false':
        return False
    if isinstance(term, list) and term[0] == '-' and len(term) == 2:
        return -int(term[1])
    return int(term)


def evaluate(term, environment):
    if isinstance(term, str):
        return environment[term] if term in environment else atom(term)
    op, *args = term
    values = [evaluate(arg, environment) for arg in args]
    if op == 'select':
        return values[0][values[1]]
    if op == 'store':
        return {**values[0], values[1]: values[2]}
    if op == 'and':
        return all(values)
    if op == 'or':
        return any(values)
    if op == 'not':
        return not values[0]
    if op == '=':
        return values[0] == values[1]
    if op == '<':
        return values[0] < values[1]
    if op == '<=':
        return values[0] <= values[1]
    if op == '>=':
        return values[0] >= values[1]
    raise ValueError('unexamined formula operator: ' + str(op))


def decode_and_check(raw, root_source):
    statements = parse_terms(raw)
    if len(statements) != 2 or statements[0] != 'sat':
        raise ValueError('expected exact SAT and get-value response')
    environment = {name: {} for name in ARRAYS}
    for key, value in statements[1]:
        value = atom(value)
        if isinstance(key, list):
            if len(key) != 3 or key[0] != 'select' or key[1] not in ARRAYS:
                raise ValueError('outside finite get-value grammar')
            environment[key[1]][int(key[2])] = value
        elif key in ['changed', 'framed', 'replacement']:
            environment[key] = value
        else:
            raise ValueError('unexpected scalar in model')
    for name in ARRAYS:
        if set(environment[name]) != {0, 1}:
            raise ValueError('missing or extra finite array entries')
        for value in environment[name].values():
            if name in ['source', 'current']:
                if type(value) is not int or not 0 <= value < 256:
                    raise ValueError('byte outside fixed full-u8 domain')
            elif type(value) is not bool:
                raise ValueError('metadata must be Boolean')
    for name in ['changed', 'framed']:
        if type(environment[name]) is not int or environment[name] not in [0, 1]:
            raise ValueError('address outside fixed two-cell integer domain')
    if type(environment['replacement']) is not int or not 0 <= environment['replacement'] < 256:
        raise ValueError('replacement outside fixed full-u8 integer domain')
    checks = [evaluate(term[1], environment) for term in parse_terms(root_source)
              if isinstance(term, list) and term and term[0] == 'assert']
    if not checks or any(value is not True for value in checks):
        raise ValueError('reported model does not satisfy every exact root assertion')
    return environment, len(checks)


def lean_literal(environment, which):
    def boolean(value):
        if type(value) is not bool:
            raise ValueError('non-Boolean Lean metadata literal')
        return 'true' if value else 'false'
    byte_values = environment[which]
    init, read, write = [environment[name] for name in
                         [which + '_init', which + '_read', 'write_authority']]
    return '⟨' + ', '.join([str(byte_values[0]), str(byte_values[1])] +
                            [boolean(a[i]) for a in [init, read, write] for i in [0, 1]]) + '⟩'


def witness_source(models):
    lines = ['import ByteLaws', 'open ByteLaws', 'namespace FreshSolverWitnesses']
    for case, environment in models.items():
        lines += [f'def {case}_s : Memory := {lean_literal(environment, "source")}',
                  f'def {case}_t : Memory := {lean_literal(environment, "current")}']
        if case == 'missing_initialization':
            proposition = f'intoWithoutInit {case}_s'
            unfold = 'intoWithoutInit'
        elif case == 'alias_frame':
            a = 'true' if environment['changed'] == 1 else 'false'
            frame = 'true' if environment['framed'] == 1 else 'false'
            proposition = f'WriteWithoutDisjoint {case}_s {a} {frame} {environment["replacement"]}'
            unfold = 'WriteWithoutDisjoint'
        elif case == 'bool_two':
            proposition = f'BoolWrongLaw {case}_s {case}_t 3'
            unfold = 'BoolWrongLaw'
        elif case == 'missing_stability':
            proposition = f'BoolWithoutStability {case}_s {case}_t'
            unfold = 'BoolWithoutStability'
        elif case == 'array_index_omission':
            proposition = f'ArrayWrongLaw {case}_s {case}_t'
            unfold = 'ArrayWrongLaw'
        else:
            raise ValueError('unexamined witness case')
        lines += [f'theorem {case}_refuted : ¬ ({proposition}) := by unfold {unfold}; decide',
                  f'#print axioms {case}_refuted']
    lines += ['end FreshSolverWitnesses']
    return '\n'.join(lines) + '\n'
