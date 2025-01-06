import xml.etree.ElementTree as ET
from copy import copy
import os
from sotalya.processing.tucuxirun import TucuCliRun, TucuPycliRun, TucuServerRun
import sotalya.processing.tucuxirun as tucuxirun


tucuxi_run = TucuPycliRun("drugfiles")
query_response = tucuxi_run.run_tucuxi_from_file("imatinib.tqf")

index = 0


def modify_num_to_0(cell_text):
    float(cell_text)
    return 0


def modify_num_to_negative(cell_text):
    value = float(cell_text)
    return -value


def multiply_values(cell_text):
    value = float(cell_text)
    return value * 1000


def modify_and_test(input_file: str, value_modifier):
    # Parse the XML file
    tree = ET.parse(input_file)
    root = tree.getroot()

    # Recursive function to process each element
    def process_element(element):
        for child in element:
            # Check if the field is an integer
            try:
                original = copy(child.text)
                child.text = str(value_modifier(child.text))
                # Write the modified tree back to a file
                global index
                index = index + 1
                output_file = "tmptqf/" + input_file + str(index)
                tree.write(output_file, encoding="utf-8", xml_declaration=True)
                print(f"Modified XML saved to {output_file}")
                query_response = tucuxi_run.run_tucuxi_from_file(output_file)
                print(f"Query status: {query_response.queryStatus.statusCode}")
                print(f"Query statusLit: {query_response.queryStatus.statusCodeLit}")
                print(f"Query description: {query_response.queryStatus.description}")
                print(f"Query message: {query_response.queryStatus.message}")

                # Back to normal
                child.text = str(original)

            except (ValueError, TypeError):
                # If not an integer or empty, skip
                pass
            # Recurse into child elements
            process_element(child)

    # Process the root element
    process_element(root)


if not os.path.exists("tmptqf"):
    os.mkdir("tmptqf")

for modifier in [modify_num_to_0, modify_num_to_negative, multiply_values]:
    modify_and_test("imatinib.tqf", modifier)
