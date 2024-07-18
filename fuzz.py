from random import randint
import subprocess

def gen_test() -> str:
    var_count = randint(1, 5)
    clause_count = randint(1, 5)
    clauses = []
    for i in range(clause_count):
        clause: list[int] = []
        while not clause:
            for i in range(var_count):
                t = randint(0, 2)
                if t == 1:
                    clause.append(i+1)
                elif t == 2:
                    clause.append(-i-1)
        clauses.append(clause)
    return ''.join([
        'p cnf ', str(var_count), ' ', str(clause_count), '\n',
        '\n'.join(' '.join(str(elem) for elem in clause + [0]) for clause in clauses),
    ])

for i in range(10000):
    with open('test.txt', 'wt') as f:
        f.write(gen_test())

    a = subprocess.run(['minisat', 'test.txt'], capture_output=True)
    b = subprocess.run(['target/debug/emilia', 'test.txt'], capture_output=True)
    sat = a.stdout.split()[-1] == b'SATISFIABLE'
    sat2 = b.stderr == b''
    if sat != sat2:
        print(sat, sat2)
        print(a.stdout.split()[-1])
        print(b.stderr)
    assert sat == sat2

