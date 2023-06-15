import sys

def wrap_raw_string(code):
    count, string = code
    return f'r{"#"*count}"{string}"{"#"*count}'

if __name__ == '__main__':
    input_file = sys.argv[1]
    lines = []
    with open(input_file, "r") as infile:
        lines = list(map(lambda x: x.rstrip(), infile.readlines()))
    case = 1
    description = f"Test {case}"
    code = []
    output = []
    insert_mode = False
    for line in lines:
        # Skip uninteresting lines
        if line.startswith(";>>") \
        or line.startswith(";;;") \
        or line.startswith(";; -") \
        or line.rstrip() == ";;":
            continue
        
        if not line:
            # New line after code+output => print out test case
            if code and output:
                assert len(code) == len(output)

                code_str = f"&[ {', '.join(map(wrap_raw_string, code))} ]"
                output_str = f"&[ {', '.join(output)} ]"
                print(f'#[test_case({code_str}, {output_str} ; r#"{description}"#)]')
                case += 1
                description = f"Test {case}"
                code = []
                output = []
            # skip line
            continue

        hash_count = line.count("#") + 1
        # Description
        if line.startswith(";; "):
            description = line[3:]
            insert_mode = False
        # Successful Output
        elif line.startswith(";=>"):
            output.append(f'Ok(r{"#"*hash_count}"{line[3:]}"{"#"*hash_count})')
            insert_mode = False
        # Failing Output
        elif line.startswith(";/"):
            output.append(f'Err(r{"#"*hash_count}"{line[3:]}"{"#"*hash_count})')
            insert_mode = False
        # Code to evaluate
        else:
            if insert_mode:
                (prev_count, prev_code) = code[-1]
                code[-1] = (max(prev_count, hash_count), f"{prev_code}\\n{line}")
            else:
                code.append((hash_count, line))
                insert_mode = True

    # while index < len(lines):
    #     while not lines[index] \
    #     or lines[index].startswith(";>>") \
    #     or lines[index].startswith(";;;") \
    #     or lines[index].startswith(";; -") \
    #     or lines[index].rstrip() == ";;":
    #         index += 1
    #     description = ""
    #     if lines[index].startswith(";; "):
    #         description = lines[index][3:]
    #         index += 1
    #     code = []
    #     output = []
    #     while lines[index] != "":
    #         code = lines[index]
    #         index += 1
    #         if lines[index].startswith(";=>"):
    #             output = lines[index][3:]
    #         elif lines[index].startswith(";/"):
    #             output = lines[index][4:-2]
    #         index += 1

    #     hash_code_count = code.count("#") + 1
    #     hash_output_count = output.count("#") + 1

    #     if description:
    #         print(f'#[test_case(r{"#" * hash_code_count}"{code}"{"#" * hash_code_count}, r{"#" * hash_output_count}"{output}"{"#" * hash_output_count} ; r#"{description}"#)]')
    #     else:
    #         print(f'#[test_case(r{"#" * hash_code_count}"{code}"{"#" * hash_code_count}, r{"#" * hash_output_count}"{output}"{"#" * hash_output_count} ; r{"#"*max(hash_code_count,hash_output_count)}"Test {case})]')
    #         case += 1

