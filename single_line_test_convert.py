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
        or lines[index].startswith(";; -") \
        or lines[index].rstrip() == ";;":
            index += 1
        description = ""
        if lines[index].startswith(";; "):
            description = lines[index][3:]
            index += 1
        code = lines[index]
        index += 1
        if lines[index].startswith(";=>"):
            output = lines[index][3:]
        elif lines[index].startswith(";/"):
            output = lines[index][4:-2]
        index += 1

        hash_code_count = code.count("#") + 1
        hash_output_count = output.count("#") + 1

        if description:
            print(f'#[test_case(r{"#" * hash_code_count}"{code}"{"#" * hash_code_count}, r{"#" * hash_output_count}"{output}"{"#" * hash_output_count} ; r#"{description}"#)]')
        else:
            print(f'#[test_case(r{"#" * hash_code_count}"{code}"{"#" * hash_code_count}, r{"#" * hash_output_count}"{output}"{"#" * hash_output_count} ; r{"#"*max(hash_code_count,hash_output_count)}"Test {case}: {code} => {output}"{"#"*max(hash_code_count,hash_output_count)})]')
            case += 1

