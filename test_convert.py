import sys


if __name__ == '__main__':
    input_file = sys.argv[1]
    lines = []
    with open(input_file, "r") as infile:
        lines = list(map(lambda x: x.rstrip(), infile.readlines()))
    index = 0
    case = 1
    while index < len(lines):
        while not lines[index] \
        or lines[index].startswith(";>>") \
        or lines[index].startswith(";;;") \
        or lines[index].startswith(";; -"):
            index += 1
        description = ""
        if lines[index].startswith(";; "):
            description = lines[index][3:].replace("\"","\\\"")
            index += 1
        code = lines[index].replace("\"","\\\"")
        index += 1
        if lines[index].startswith(";=>"):
            output = lines[index][3:].replace("\"","\\\"")
        index += 1

        if description:
            print(f'#[test_case("{code}", "{output}" ; "{description}")]')
        else:
            print(f'#[test_case("{code}", "{output}" ; "Test #{case}: {code} => {output}")]')
            case += 1

