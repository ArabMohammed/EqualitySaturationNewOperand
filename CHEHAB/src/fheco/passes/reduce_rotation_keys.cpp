#include "fheco/ir/func.hpp"
#include "fheco/ir/term.hpp"
#include "fheco/passes/reduce_rotation_keys.hpp"
#include "fheco/util/common.hpp"
#include <algorithm>
#include <cstdlib>
#include <functional>
#include <stdexcept>
#include <iostream>

using namespace std;

namespace fheco::passes
{


/********************************************************************************************************************/
/********************************************************************************************************************
unordered_set<int> reduce_rotation_keys(const shared_ptr<ir::Func> &func, size_t keys_threshold)
{
  //std::cout<<"\n\n Welcome in reducing rotation step keys \n";
  unordered_map<int, int> steps_freq;
  ir::Term::PtrSet decomp_candidate_terms; // to store terms with steps that are not power of two  
  for (auto term : func->get_top_sorted_terms())
  {
    if (term->type() == ir::Term::Type::cipher && term->op_code().type() == ir::OpCode::Type::rotate)
    {
      auto steps = term->op_code().steps();
      ++steps_freq[steps]; 
      if (!util::is_power_of_two(abs(steps)))
        decomp_candidate_terms.insert(func->data_flow().get_term(term->id()));
    }
  }
  //std::cout<<"number of candidates terms to decompose :"<<decomp_candidate_terms.size()<<"\n";
  vector<int> ordered_used_steps;
  ordered_used_steps.reserve(steps_freq.size());
  for (const auto &e : steps_freq)
    ordered_used_steps.push_back(e.first);

  int keys_count = ordered_used_steps.size();
  std::cout<<"\n";
  if (keys_count <= keys_threshold)
    return unordered_set(ordered_used_steps.begin(), ordered_used_steps.end());

  unordered_map<int, vector<int>> steps_nafs;
  // ordered_used_steps = [6,8,16,32,15]
  for (auto steps : ordered_used_steps)
  {
    if (util::is_power_of_two(abs(steps)))
      steps_nafs.emplace(steps, vector<int>{steps});
    else
      steps_nafs.emplace(steps, naf(steps));
  }
  //*************************store the naf cost of each step **********************
  // * (if the step is power of two it cost will be 0) 
  //    else the cost =  frepuency of the step multiplied * (size_naf_reprentation - 1) 

  unordered_map<int, int> steps_costs;
  for (const auto &e : steps_freq)
  {
    auto steps = e.first;
    auto freq = e.second;
    steps_costs.emplace(steps, freq * (steps_nafs.at(steps).size() - 1));
  }
  //*************Sorting the ordered_used_steps **********************    
  // this case happen if we havent looped over all ordered_used_steps vector 
  //*****************************************************************
  sort(ordered_used_steps.begin(), ordered_used_steps.end(), [&steps_costs, &steps_nafs](int lhs, int rhs) {
    auto lhs_cost = steps_costs.at(lhs);
    auto rhs_cost = steps_costs.at(rhs);
    if (lhs_cost == rhs_cost)
      //step with the smaller NAF size comes first
      return steps_nafs.at(lhs) < steps_nafs.at(rhs);
    //If the costs are not equal, 
    //the step with the higher cost is placed first
    return lhs_cost > rhs_cost;
  });
  //*******************************************************************
  unordered_set<int> steps_to_decomp;
  unordered_set<int> used_steps;
  int init_steps_count = ordered_used_steps.size();
  //std::cout<<"Prepating the used_steps list : \n";
  for (size_t i = 0; i < init_steps_count; ++i)
  {
    auto min_cost_steps = ordered_used_steps.back();
    if (util::is_power_of_two(abs(min_cost_steps)))
    {
      //std::cout<<"This step is power of two \n";
      used_steps.insert(min_cost_steps);
      ordered_used_steps.pop_back();//remove the last elem
      continue;
    }
    // min_cost_steps not a power of two 
    steps_to_decomp.insert(min_cost_steps);
    ordered_used_steps.pop_back();//remove the last elem
    //   int keys_count = ordered_used_steps.size(); Initialization 
    keys_count -= 1;
    for (auto naf_comp : steps_nafs.at(min_cost_steps))
    {
      auto [it, inserted] = used_steps.insert(naf_comp);
      if (inserted)
        keys_count += 1;
    }
    if (keys_count <= keys_threshold)
      break;
  }
  if (keys_count > keys_threshold)
    throw logic_error("could not go lower than the threshold, maybe keys_threshold is invalid (too low)");
  //std::cout<<"Insert remaining non inserted steps: \n\n";
  for (auto non_decomp_steps : ordered_used_steps)
    used_steps.insert(non_decomp_steps);
  
  // greater<int>() is a standard comparator function object that sorts the elements in descending order
  // sort the elements in the vectors associated with each step
  for (auto steps : steps_to_decomp)
    sort(steps_nafs.at(steps).begin(), steps_nafs.at(steps).end(), greater<int>());
  //**************************************************
  //std::cout<<"\n updating terms needing decomposition :\n";
  for (auto term : decomp_candidate_terms)
  {
    auto steps = term->op_code().steps();
    //std::cout<<steps<<" ";
    // update terms of rotations that needs decomposition 
    if (steps_to_decomp.find(steps) != steps_to_decomp.end())
      decomp_rotation_term(func, term, steps_nafs.at(steps));
  }
  //std::cout<<"\n";
  return used_steps;
}
/*****************************************************************************************/
/******************************************************************************************/
unordered_set<int> reduce_rotation_keys(const shared_ptr<ir::Func> &func, size_t keys_threshold)
{
  unordered_map<int, int> steps_freq;
  ir::Term::PtrSet decomp_candidate_terms;
  for (auto term : func->get_top_sorted_terms())
  {
    if (term->type() == ir::Term::Type::cipher && term->op_code().type() == ir::OpCode::Type::rotate)
    {
      auto steps = term->op_code().steps();
      ++steps_freq[steps];
      if (!util::is_power_of_two(abs(steps)))
        decomp_candidate_terms.insert(func->data_flow().get_term(term->id()));
    }
  }

  vector<int> ordered_used_steps;
  ordered_used_steps.reserve(steps_freq.size());
  for (const auto &e : steps_freq)
    ordered_used_steps.push_back(e.first);

  int keys_count = ordered_used_steps.size();
  if (keys_count <= keys_threshold)
    return unordered_set(ordered_used_steps.begin(), ordered_used_steps.end());

  unordered_map<int, vector<int>> steps_nafs;
  for (auto steps : ordered_used_steps)
  {
    if (util::is_power_of_two(abs(steps)))
      steps_nafs.emplace(steps, vector<int>{steps});
    else
      steps_nafs.emplace(steps, naf(steps));
  }

  unordered_map<int, int> steps_costs;
  for (const auto &e : steps_freq)
  {
    auto steps = e.first;
    auto freq = e.second;
    steps_costs.emplace(steps, freq * (steps_nafs.at(steps).size() - 1));
  }

  sort(ordered_used_steps.begin(), ordered_used_steps.end(), [&steps_costs, &steps_nafs](int lhs, int rhs) {
    auto lhs_cost = steps_costs.at(lhs);
    auto rhs_cost = steps_costs.at(rhs);
    if (lhs_cost == rhs_cost)
      return steps_nafs.at(lhs) < steps_nafs.at(rhs);

    return lhs_cost > rhs_cost;
  });
  unordered_set<int> steps_to_decomp;
  unordered_set<int> used_steps;
  int init_steps_count = ordered_used_steps.size();
  for (size_t i = 0; i < init_steps_count; ++i)
  {
    auto min_cost_steps = ordered_used_steps.back();
    if (util::is_power_of_two(abs(min_cost_steps)))
    {
      used_steps.insert(min_cost_steps);
      ordered_used_steps.pop_back();
      continue;
    }
    steps_to_decomp.insert(min_cost_steps);
    ordered_used_steps.pop_back();
    keys_count -= 1;
    for (auto naf_comp : steps_nafs.at(min_cost_steps))
    {
      auto [it, inserted] = used_steps.insert(naf_comp);
      if (inserted)
        keys_count += 1;
    }
    if (keys_count <= keys_threshold)
      break;
  }
  if (keys_count > keys_threshold)
    throw logic_error("could not go lower than the threshold, maybe keys_threshold is invalid (too low)");

  for (auto non_decomp_steps : ordered_used_steps)
    used_steps.insert(non_decomp_steps);

  for (auto steps : steps_to_decomp)
    sort(steps_nafs.at(steps).begin(), steps_nafs.at(steps).end(), greater<int>());
  for (auto term : decomp_candidate_terms)
  {
    auto steps = term->op_code().steps();
    if (steps_to_decomp.find(steps) != steps_to_decomp.end())
      decomp_rotation_term(func, term, steps_nafs.at(steps));
  }

  return used_steps;
}
/*******************************************************************************************/

void decomp_rotation_term(const shared_ptr<ir::Func> &func, ir::Term *term, const vector<int> &steps_seq)
{
  if (term->op_code().type() != ir::OpCode::Type::rotate)
    throw invalid_argument("term must be a rotation term");

  auto arg = term->operands()[0];
  for (auto steps : steps_seq)
  {
    if (steps == 0 || abs(steps) == func->slot_count())
      continue;

    auto rotation_comp = func->insert_op_term(ir::OpCode::rotate(steps), {arg});
    arg = rotation_comp;
  }
  if (*arg != *term->operands()[0])
    func->replace_term_with(term, arg);
}
/*******************************************************************************************/
/*******************************************************************************************/
vector<int> naf(int value)
{
  vector<int> res;

  // Record the sign of the original value and compute abs
  bool sign = value < 0;
  value = abs(value);

  // Transform to non-adjacent form (NAF)
  for (int i = 0; value; i++)
  {
    int zi = (value & int(0x1)) ? 2 - (value & int(0x3)) : 0;
    value = (value - zi) >> 1;
    if (zi)
      res.push_back((sign ? -zi : zi) * (1 << i));
  }

  return res;
}
} // namespace fheco::passes