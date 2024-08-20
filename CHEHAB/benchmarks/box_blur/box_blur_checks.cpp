#include "fheco/fheco.hpp"
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <ostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;
using namespace fheco;

void box_blur(size_t width)
{
  vector<vector<integer>> kernel = {{1, 1, 1}, {1, 1, 1}, {1, 1, 1}};
  Ciphertext img("img", 0, 255);
  Ciphertext top_row = img >> width;
  Ciphertext bottom_row = img << width;
  Ciphertext top_sum = kernel[0][0] * (top_row >> 1) + kernel[0][1] * top_row + kernel[0][2] * (top_row << 1);
  Ciphertext curr_sum = kernel[1][0] * (img >> 1) + kernel[1][1] * img + kernel[1][2] * (img << 1);
  Ciphertext bottom_sum =
    kernel[2][0] * (bottom_row >> 1) + kernel[2][1] * bottom_row + kernel[2][2] * (bottom_row << 1);
  Ciphertext result = top_sum + curr_sum + bottom_sum;
  result.set_output("result");
}

void box_blur_baseline(size_t width)
{
  Ciphertext img("img", 0, 255);
  Ciphertext top_sum = (img >> (width + 1)) + (img >> width) + (img >> (width - 1));
  Ciphertext curr_sum = (img >> 1) + img + (img << 1);
  Ciphertext bottom_sum = (img << (width - 1)) + (img << width) + (img << (width + 1));
  Ciphertext result = top_sum + curr_sum + bottom_sum;
  result.set_output("result");
}

void print_bool_arg(bool arg, const string &name, ostream &os)
{
  os << (arg ? name : "no_" + name);
}

int main(int argc, char **argv)
{
  bool call_quantifier = false;
  if (argc > 1)
    call_quantifier = stoi(argv[1]);

  auto axiomatic = false;
  if (argc > 2)
    axiomatic = stoi(argv[2]) ? true : false;

  bool cse = true;
  if (argc > 3)
    cse = stoi(argv[3]);

  bool const_folding = true;
  if (argc > 4)
    const_folding = stoi(argv[4]);

  print_bool_arg(call_quantifier, "quantifier", clog);
  clog << " ";
  print_bool_arg(cse, "cse", clog);
  clog << " ";
  print_bool_arg(const_folding, "constant_folding", clog);
  clog << '\n';

  string app_name = "box_blur";
  size_t width = 64;
  size_t height = 64;
  size_t slot_count = width * height;
  int bit_width = 20;
  bool signdness = false;
  bool need_cyclic_rotation = true;

  clog << "\nnoopt function\n";
  string noopt_func_name = app_name + "_noopt";
  const auto &noopt_func =
    Compiler::create_func(noopt_func_name, slot_count, bit_width, signdness, need_cyclic_rotation);
  box_blur(width);

  string noopt_gen_name = "gen_he_" + noopt_func_name;
  string noopt_gen_path = "he/" + noopt_gen_name;
  ofstream noopt_header_os(noopt_gen_path + ".hpp");
  if (!noopt_header_os)
    throw logic_error("failed to create noopt_header file");

  ofstream noopt_source_os(noopt_gen_path + ".cpp");
  if (!noopt_source_os)
    throw logic_error("failed to create noopt_source file");

  Compiler::gen_he_code(noopt_func, noopt_header_os, noopt_gen_name + ".hpp", noopt_source_os);

  ofstream noopt_ir_os(noopt_func_name + "_ir.dot");
  if (!noopt_ir_os)
    throw logic_error("failed to create noopt_ir file");

  util::draw_ir(noopt_func, noopt_ir_os);
  util::Quantifier noopt_quantifier(noopt_func);
  if (call_quantifier)
  {
    cout << "\ninitial circuit characteristics\n";
    noopt_quantifier.run_all_analysis();
    noopt_quantifier.print_info(cout);
    cout << endl;
  }

  clog << "\nopt function\n";
  if (cse)
  {
    Compiler::enable_cse();
    Compiler::enable_order_operands();
  }
  else
  {
    Compiler::disable_cse();
    Compiler::disable_order_operands();
  }

  if (const_folding)
    Compiler::enable_const_folding();
  else
    Compiler::disable_const_folding();

  string opt_func_name = app_name + "_opt";
  const auto &opt_func = Compiler::create_func(opt_func_name, slot_count, bit_width, signdness, need_cyclic_rotation);
  box_blur(width);

  string opt_gen_name = "gen_he_" + opt_func_name;
  string opt_gen_path = "he/" + opt_gen_name;
  ofstream opt_header_os(opt_gen_path + ".hpp");
  if (!opt_header_os)
    throw logic_error("failed to create opt_header file");

  ofstream opt_source_os(opt_gen_path + ".cpp");
  if (!opt_source_os)
    throw logic_error("failed to create opt_source file");
  auto window = 0;
  Compiler::compile(opt_func, opt_header_os, opt_gen_name + ".hpp", opt_source_os, axiomatic,window);

  auto noopt_obtained_outputs = util::evaluate_on_clear(noopt_func, opt_func->get_inputs_example_values());
  auto opt_obtained_outputs = util::evaluate_on_clear(opt_func, noopt_func->get_inputs_example_values());
  if (
    noopt_obtained_outputs != opt_func->get_outputs_example_values() ||
    opt_obtained_outputs != noopt_func->get_outputs_example_values())
    throw logic_error("compilation correctness-test failed");

  ofstream io_example_os(app_name + "_io_example.txt");
  if (!io_example_os)
    throw logic_error("failed to create io_example file");

  util::print_io_terms_values(noopt_func, io_example_os);
  ofstream opt_ir_os(opt_func_name + "_ir.dot");
  if (!opt_ir_os)
    throw logic_error("failed to create opt_ir file");

  util::draw_ir(opt_func, opt_ir_os);
  if (call_quantifier)
  {
    cout << "\nfinal circuit characteristics\n";
    util::Quantifier opt_quantifier(opt_func);
    opt_quantifier.run_all_analysis();
    opt_quantifier.print_info(cout);

    cout << "\nimprovment rates\n";
    auto diff_quantifier = (noopt_quantifier - opt_quantifier) / noopt_quantifier * 100;
    diff_quantifier.print_info(cout);
  }
  return 0;
}
