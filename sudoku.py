import itertools
import json
import sys


def exactly_one(x: list[int]) -> list[list[int]]:
    ret = []
    ret.append(x[:])
    for a, b in itertools.combinations(x, 2):
        ret.append([-a, -b])
    return ret


def pos(x: int, y: int, v: int):
    return ((x * 9) + y) * 9 + v + 1


def print_sudoku_rules():
    c = []

    for a in range(9):
        for b in range(9):
            c.extend(exactly_one([pos(a, b, i) for i in range(9)]))
            c.extend(exactly_one([pos(a, i, b) for i in range(9)]))
            c.extend(exactly_one([pos(i, a, b) for i in range(9)]))

    for a in range(0, 9, 3):
        for b in range(0, 9, 3):
            for v in range(9):
                c.extend(
                    exactly_one(
                        [pos(q, w, v) for q in range(a, a + 3) for w in range(b, b + 3)]
                    )
                )

    print("p cnf", 9 * 9 * 9, len(c))
    for cl in c:
        print(*cl, 0)


def print_sudoku(sudoku: list[list[int]]):
    assert len(sudoku) == 9
    for i, line in enumerate(sudoku):
        assert len(line) == 9
        for j, x in enumerate(line):
            if x:
                print(pos(j, i, x - 1), 0)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1] == 'to_sat':
        print_sudoku_rules()
        print_sudoku(
            [
                list(map(lambda x: int(x) if x.isdecimal() else 0, input()))
                for i in range(9)
            ]
        )
    else:
        assert sys.argv[1] == 'from_sat'
        sat_ans = json.loads(input())
        ans: list[list[int | None]] = [[None for i in range(9)] for j in range(9)]

        for x in range(9):
            for y in range(9):
                for v in range(9):
                    if sat_ans[pos(x, y, v) - 1]:
                        if ans[y][x] != None:
                            assert False
                        ans[y][x] = v + 1

        for row in range(9):
            assert len(set(ans[row][i] for i in range(9))) == 9
        for col in range(9):
            assert len(set(ans[i][col] for i in range(9))) == 9
        for square in range(0, 9):
            assert (
                len(
                    set(
                        ans[square // 3 * 3 + i // 3][square % 3 * 3 + i % 3]
                        for i in range(9)
                    )
                )
                == 9
            )

        for r in ans:
            print(*r)
