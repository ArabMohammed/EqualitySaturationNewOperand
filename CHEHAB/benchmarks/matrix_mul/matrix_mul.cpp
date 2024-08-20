#include "fheco/fheco.hpp"
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;
using namespace fheco;

Ciphertext reduce_add_lin(const Ciphertext &x, int vector_size)
{
  Ciphertext result = x;
 /*  for (int i = vector_size -1 ; i > 0; --i)
  {
    result += x <<i;
  } */
  for (int i = 1 ; i < vector_size; ++i)
  {
    result += x <<i;
  }
  return result;
}

void print_bool_arg(bool arg, const string &name, ostream &os)
{
  os << (arg ? name : "no_" + name);
}

void matrix_mul(int m_a, int n_b, int n_a_m_b)
{
  // declare inputs
  vector<Ciphertext> A_row_encrypted;
  vector<Ciphertext> B_column_encrypted;
  // encrypt by line for matrix A
  for (int i = 0; i < m_a; ++i)
  {
    //
    Ciphertext line("A[" + to_string(i) + "][]");
    A_row_encrypted.push_back(line);
  }
  // encrypt by column for matrix B
  for (int i = 0; i < n_b; ++i)
  {
    Ciphertext column("B[][" + to_string(i) + "]");
    B_column_encrypted.push_back(column);
  }

  // compute
  vector<Ciphertext> C_row_encrypted;
  for (size_t i = 0; i < A_row_encrypted.size(); ++i)
  {
    Ciphertext cline;
    for (size_t j = 0; j < B_column_encrypted.size(); ++j)
    {
      vector<int64_t> mask(A_row_encrypted.size(), 0);
      mask[j] = 1;
      Ciphertext slot;
      ///************************************************ 
      slot = SumVec(A_row_encrypted[i] * B_column_encrypted[j],n_b);
      ///***********************************************************
      if (j == 0)
        cline = slot * mask;
      else
        cline += slot * mask;
    }
    cline.set_output("C[" + to_string(i) + "][]");
    C_row_encrypted.push_back(cline);
  }
}

int main(int argc, char **argv)
{

  auto axiomatic = false;
  if (argc > 1)
    axiomatic = stoi(argv[1]) ? true : false;

  auto window = 0;
  if (argc > 2)
    window = stoi(argv[2]);

  bool call_quantifier = false;
  if (argc > 3)
    call_quantifier = stoi(argv[3]);
  bool cse = true;
  if (argc > 4)
    cse = stoi(argv[4]);

  bool const_folding = true;
  if (argc > 5)
    const_folding = stoi(argv[5]);

  print_bool_arg(call_quantifier, "quantifier", clog);
  clog << " ";
  print_bool_arg(cse, "cse", clog);
  clog << " ";
  print_bool_arg(const_folding, "constant_folding", clog);
  clog << '\n';

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

  chrono::high_resolution_clock::time_point t;
  chrono::duration<double, milli> elapsed;
  t = chrono::high_resolution_clock::now();
  string func_name = "matrix_mul" ;
  /******************************/
  size_t slot_count = 128;
  int m_a = slot_count;
  int n_a_m_b = slot_count;
  int n_b = slot_count;
  /*****************************/
  const auto &func = Compiler::create_func(func_name, slot_count, 20, true, true);
  matrix_mul(m_a, n_b, n_a_m_b);
  string gen_name = "_gen_he_" + func_name;
  string gen_path = "he/" + gen_name;
  ofstream header_os(gen_path + ".hpp");
  if (!header_os)
    throw logic_error("failed to create header file");

  ofstream source_os(gen_path + ".cpp");
  if (!source_os)                         
    throw logic_error("failed to create source file");
  /////////////////////
  /*auto ruleset = Compiler::Ruleset::joined;
  if (argc > 2)
    ruleset = static_cast<Compiler::Ruleset>(stoi(argv[2]));
  auto rewrite_heuristic = trs::RewriteHeuristic::bottom_up;
  if (argc > 3)
    rewrite_heuristic = static_cast<trs::RewriteHeuristic>(stoi(argv[3]));
  Compiler::compile(func, ruleset, rewrite_heuristic, header_os, gen_name + ".hpp", source_os, true);*/
  /////////////////////////////
  Compiler::compile(func, header_os, gen_name + ".hpp", source_os, axiomatic, window);
  elapsed = chrono::high_resolution_clock::now() - t;
  cout << elapsed.count() << " ms\n";

  if (call_quantifier)
  {
    util::Quantifier quantifier{func};
    quantifier.run_all_analysis();
    quantifier.print_info(cout);
  }
  return 0;
}
