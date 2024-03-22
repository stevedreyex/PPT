#include <bits/stdc++.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include <isl/arg.h>
#include <isl/ctx.h>
#include <isl/options.h>
#include <isl/schedule_node.h>

#include "ppcg/pet/options.h"
#include "ppcg/pet/scop.h"
#include "ppcg/pet/scop_yaml.h"

// Define a macro for error handling
#define CHECK_NULL(pointer, message) \
    if ((pointer) == NULL) { \
        fprintf(stderr, "Error: %s\n", message); \
        return -1; \
    }

char *prog_path;    // argv[1]
char *ppcg_launch;  // argv[2]

typedef enum isl_schedule_node_type isl_schedule_node_type;

typedef struct {
  /* name of the loop index from S[ x, x, x ... ] */
  char *index;
  /* May be less than or equal less than. */
  int is_lt;
  /* May be greater than or equal greater than. */
  int is_gt;
  char *ub;
  char *lb;
  long int ub_val;
  long int lb_val;
} indexBound;

typedef struct  {
  /* Which statement? */
  int stmt_no;
  /* the {Sn[x, x, x, ...] : constraints ; ... }, the x part, vars for inequality */
  char **names;
  /* Number of indexBound, also the number of stmts (in dom) */
  int ib_num;
  /* the constraint part, the constraint for each stmt */
  indexBound** ib;
} stmtSpace;

typedef struct {
  /* The number of the statement */
  int stmt_num;
  /* Number of undetermined vars */
  int var_num;
  /* The address of the statement */
  stmtSpace **stmt;
  /* the [x, x, x, ...] -> { ... }, the x part, vars for inequality */
  char **variables;
} domainSpace;

typedef struct extTree extTree;
struct extTree {
  isl_schedule_node_type type;
  /* All data to construct the Tree */
  domainSpace *dom;
  /* The ancestor fo the tree node */
  extTree *parent;
  /* The children of the tree node */
  extTree **children;
  /* The number of children */
  int child_num;
  /* Current at which children */
  int curr_child;
} ;

#define BUFFER_SIZE 1024 // Increased buffer size

/* The initializer starts */
indexBound *init_indexBound() {
  indexBound *bound = (indexBound *)(malloc(sizeof(indexBound)));
  bound->index = NULL;
  bound->is_lt = 0;
  bound->is_gt = 0;
  bound->ub = NULL;
  bound->lb = NULL;
  bound->ub_val = -1;
  bound->lb_val = -1;
  return bound;
}

stmtSpace *init_stmtSpace(int stmt_no, int ib_num) {
  stmtSpace *stmt = (stmtSpace *)(malloc(sizeof(stmtSpace)));
  stmt->stmt_no = stmt_no;
  stmt->ib_num = ib_num;
  stmt->names = (char **)(malloc(10 * sizeof(char *)));
  stmt->ib = (indexBound **)(malloc(10 * sizeof(indexBound *)));
  return stmt;
}

domainSpace *init_domainSpace() {
  domainSpace *dom = (domainSpace *)(malloc(sizeof(domainSpace)));
  dom->stmt_num = 0;
  dom->var_num = 0;
  dom->stmt = (stmtSpace **)(malloc(10 * sizeof(stmtSpace *)));
  dom->variables = (char **)(malloc(10 * sizeof(char *)));
  return dom;
}

extTree *init_extTree(domainSpace *dom, extTree *parent) {
  extTree *tree = (extTree *)(malloc(sizeof(extTree)));
  tree->dom = dom;
  tree->parent = parent;
  tree->children = (extTree **)(malloc(10 * sizeof(extTree *)));
  tree->child_num = 0;
  tree->curr_child = 0;
  return tree;
}

/*
 * Parse the DWARF information from the binary
 * @param out char **unit: the array of compiled source path
 * @return int: number of compilation unit
 */
int parse_dwarf(char **unit, FILE *fp) {

  int compilation_unit = 0;
  char path[1035];
  char prev_line[1035] = "";
  
  //init the array, assume there's only 10 compilation unit
  for (int i = 0; i < 10; i++) {
    unit[i] = NULL;
  }

  // Read the output line by line and process it
  while (fgets(path, sizeof(path), fp) != NULL) {
      // Check if the current line contains DW_AT_name
      // printf("%s\n\n", path);
      // Check if the previous line contains DW_AT_comp_dir
      if (strstr(prev_line, "DW_AT_name") != NULL) {
          // Print DW_AT_name and DW_AT_comp_dir
      }
      if (strstr(path, "DW_AT_comp_dir") != NULL) {
        // printf("touched\n");
        // printf("%s", prev_line);
        // printf("%s", path);
        char *colon_pos_name = strchr(prev_line, ':');
        for (int i = 0; i < 2 && colon_pos_name != NULL; i++) {
            colon_pos_name = strchr(colon_pos_name + 1, ':');
        }
        colon_pos_name += 2;
        colon_pos_name[strcspn(colon_pos_name, "\n")] = '\0';
        if (colon_pos_name != NULL) {
            // is a inclue path
            if (compilation_unit) {
                unit[compilation_unit] = (char *)(malloc(strlen(colon_pos_name) + 1));
                // copy content and discard contents after 
                char *last_slash = strrchr(colon_pos_name, '/');
                if (last_slash != NULL) {
                    //remove last_slash in colon_pos_name
                    *last_slash = '\0';
                } 
                strcpy(unit[compilation_unit], colon_pos_name);
            // Where tha main at
            } else {
                unit[compilation_unit] = (char *)(malloc(strlen(colon_pos_name) + 1));
                strcpy(unit[compilation_unit], colon_pos_name);
            }
            compilation_unit++;
        }
      }
      // Save the current line to prev_line
      strcpy(prev_line, path);
  }

  // Close the pipe
  pclose(fp);
  return compilation_unit;
}

void replaceString(char *str, const char *oldSubstr, const char *newSubstr) {
    char *pos = strstr(str, oldSubstr);
    if (pos != NULL) {
        int oldSubstrLen = strlen(oldSubstr);
        int newSubstrLen = strlen(newSubstr);
        memmove(pos + newSubstrLen, pos + oldSubstrLen, strlen(pos + oldSubstrLen) + 1);
        memcpy(pos, newSubstr, newSubstrLen);
    }
}

/*
 * Instead of calculating the schedule from the pet_scop, we can use ppcg to do that
 * @param out char *arg_list: the list of argument to pass to ppcg
 * @param int compilation_unit: the number of compilation unit
 * @return int arg_count: the number of arguments for ppcg
 */
int get_computed_sched_from_ppcg(char **unit, char *ret, int compilation_unit) {
  // with -I flag, at least 2x
  
  int arg_count = 0;
  char *arg_list[2*compilation_unit];
  const char *incl = "-I";

  // arg_list[arg_count] = argv[0];
  // arg_count++;
  char ppcg_args[BUFFER_SIZE/2] = {0};
  char ppcg_call[BUFFER_SIZE] = {0};

  // Concatenate all args to make a ppcg call
  for (int i = 0; i < compilation_unit; i++) {
    if (i)
      strcat(ppcg_args, incl);
    strcat(ppcg_args, unit[i]);
    strcat(ppcg_args, " ");
    arg_count++;
  }

  char sched[BUFFER_SIZE/4];
  strcpy(sched, prog_path);
  char newSubstr[] = "/schedule/";
  char addition[] = ".sched";
  
  // Step 1: Replace "/obj/" with "/schedule/"
  replaceString(sched, "/obj/", newSubstr);

  // Step 2: Append "sched" at the end
  strcat(sched, addition);
  // strcat(ppcg_call, "--save-schedule=/home/dreyex/use_this/schedule/jacobi-2d.sched");
  
  // A "--no-reschedule" flag is added to prevent ppcg from rescheduling the program
  snprintf(ppcg_call, BUFFER_SIZE-1, "%s %s --no-reschedule --save-schedule=%s", ppcg_launch, ppcg_args, sched);
  #ifdef DEBUG
  printf("ppcg call: %s\n", ppcg_call);
  #endif
  FILE *fp;
  fp = popen(ppcg_call, "r");
  if (fp == NULL) {
      printf("Failed to run command\n");
      ret = NULL;
  } else {
    strcpy(ret, sched);
  }
  pclose(fp);

  return arg_count;
}

std::list<std::string> split(const std::string &s, const char delimiter, 
                             const std::string start, const std::string end) {
  size_t start_pos = 0;
  size_t end_pos = 0;
  std::list<std::string> tokens;
  std::string token;
  std::string *parse_arget = new std::string(s);
  start_pos = parse_arget->find(start);
  end_pos = parse_arget->find(end);
  token = parse_arget->substr(start_pos + 1, end_pos - start_pos - 1);
  std::istringstream tokenStream(token);
  // while (std::getline(tokenStream, token, delimiter)) {
  for (std::string token; std::getline(tokenStream, token, delimiter);){
    // if token starts or ends with space, remove it
    if (token[0] == ' ') {
      token.erase(0, 1);
    }
    if (token[token.length() - 1] == ' ') {
      token.erase(token.length() - 1, 1);
    }
    tokens.push_back(token);
  }
  return tokens;
}

std::list<std::string> split_by_str(const std::string &s, const std::string delimiter, 
                                    const std::string start, const std::string end) {
  size_t start_pos = 0;
  size_t end_pos = 0;
  std::list<std::string> tokens;
  std::string token;
  std::string *parse_arget = new std::string(s);
  start_pos = parse_arget->find(start);
  end_pos = parse_arget->find(end);
  token = parse_arget->substr(start_pos + 1, end_pos - start_pos - 1);
  while (token.find(delimiter) != std::string::npos) {
    size_t pos = token.find(delimiter);
    tokens.push_back(token.substr(0, pos));
    token.erase(0, pos + delimiter.length());
  }
  tokens.push_back(token);
  return tokens;
}

inline void parse_inequality(const std::string &s, stmtSpace *stmt){
  // std::cout << "S" << stmt->stmt_no << " parsing: " << s  << "(whole token)" << std::endl; 
  std::string tok = "<";
  int occurrences = 0;
  size_t pos = 0;
  size_t temp = 0;
  size_t index_pos = std::string::npos;
  int index_var = -1;
  // Find which index this inequality is for
  /* Some Rules I've figured out later: 
   * The index var comes first than the bound var in the inequality
   * But constant bound is not limited to this rule
   * So we need to find the index var that have the smaller index_pos
   * Rather than the first one we've found
   */
  for (int i = 0; i < stmt->ib_num; i++) {
    temp = s.find(stmt->names[i]);
    if (temp < index_pos) {
      // This is the index
      index_pos = temp;
      index_var = i;
    }
  }
  if (index_var == -1) {
    std::cout << "Error: index_var not found" << std::endl;
    return;
  }
  // std::cout << "handle: " << stmt->names[index_var] << std::endl;

  // Find which inequality it is (2 or 3 elements?)
  while ((pos = s.find(tok, pos )) != std::string::npos) {
          ++ occurrences;
          pos += tok.length();
  }
  // std::cout << "occurrences: " << occurrences << std::endl;

  if (occurrences == 2) {
    // Find contents from initial to the first "<"
    size_t pos = s.find("<");
    // Start from 1, bypass the space
    std::string elem = s.substr(1, pos-1);
    stmt->ib[index_var]->lb = (char *)(malloc(elem.length() + 1));
    strcpy(stmt->ib[index_var]->lb, elem.c_str());
    // If the next char is "=", then it's less than or equal
    if (s[pos + 1] == '=') 
      stmt->ib[index_var]->is_lt = 0;
    else
      stmt->ib[index_var]->is_lt = 1;
    // Find contents from the second "<" to the end 
    pos = s.find("<", pos + 1);
    if (s[pos + 1] == '=') {
      stmt->ib[index_var]->is_gt = 0;
      // Bypass the "="
      pos++;
    }
    else
      stmt->ib[index_var]->is_gt = 1;
    // Bypass the " "
    pos++;
    elem = s.substr(pos + 1, s.length() - pos - 1);
    stmt->ib[index_var]->ub = (char *)(malloc(elem.length() + 1));
    strcpy(stmt->ib[index_var]->ub, elem.c_str());
    // If the next char is "=", then it's less than or equal
  } 
  else {
    // Occurrence == 1 or 0, since "<" not exists in ">" case
    size_t pos = s.find("=");
    int big = -1;
    // The founded one is smaller
    s.find(">") > s.find("<") ? big = 0 : big = 1;
    // std::cout << "big: " << big << std::endl;
    if (pos == std::string::npos) // Very sure is gt or lt
      big ? stmt->ib[index_var]->is_lt = 1 : stmt->ib[index_var]->is_gt = 1;
    else
      big ? stmt->ib[index_var]->is_lt = 0 : stmt->ib[index_var]->is_gt = 0;
    // std::cout << "is_lt: " << stmt->ib[index_var]->is_lt << std::endl;
    // std::cout << "is_gt: " << stmt->ib[index_var]->is_gt << std::endl;
    big ? pos = s.find(">") : pos = s.find("<");
    // std::cout << "pos: " << pos << std::endl;
    // get over the sign, take the val
    std::string elem = s.substr(pos+2, s.size());
    // std::cout << "elem: " << elem << std::endl;
    big ? stmt->ib[index_var]->lb = (char *)(malloc(elem.length() + 1)) : 
          stmt->ib[index_var]->ub = (char *)(malloc(elem.length() + 1));
    big ? strcpy(stmt->ib[index_var]->lb, elem.c_str()) :
          strcpy(stmt->ib[index_var]->ub, elem.c_str());
  }
}

inline void compensate(stmtSpace *stmt, int index, int is_ub){
  if (is_ub) {
    // Upper bound is null? Might be someone's lower bound
    for (int i = 0; i < stmt->ib_num; i++) {
      if (stmt->ib[i]->lb != NULL && !strcmp(stmt->ib[i]->lb, stmt->ib[index]->index)) {
        stmt->ib[index]->ub = (char *)(malloc(strlen(stmt->ib[i]->ub) + 1));
        strncpy(stmt->ib[index]->ub, stmt->ib[i]->ub, strlen(stmt->ib[i]->ub));
      }
    }
  } else {
    // Lower bound is null
    for (int i = 0; i < stmt->ib_num; i++) {
      if (stmt->ib[i]->ub != NULL && !strcmp(stmt->ib[i]->ub, stmt->ib[index]->index)) {
        stmt->ib[index]->lb = (char *)(malloc(strlen(stmt->ib[i]->lb) + 1));
        strncpy(stmt->ib[index]->lb, stmt->ib[i]->lb, strlen(stmt->ib[i]->lb));
      }
    }
  }
}

/*
 * Extract the domain each statement from the schedule
 * @param in FILE *file: the file to extract the domain from
 * @param out stmtSpace *dom: the domain of each statement
 */
int extract_dom_from_sched(FILE *file, domainSpace *dom) {
  char line[BUFFER_SIZE];
  int var_num = 0;
  int status = 0;
  // We only get the first line of the file and parse it
  fgets(line, sizeof(line), file);
  // Starts to parse the domain
  // Some input like this: 
  // domain: "[tsteps, n] -> { S1[t, i, j] : 0 <= t < tsteps and 0 < i <= -2 + n and 0 < j <= -2 + n; S2[t, i, j] : 0 <= t < tsteps and 0 < i <= -2 + n and 0 < j <= -2 + n }"
  // First parse the variable part: [tsteps, n]
  std::cout << "start parsing line: " << line << std::endl;
  std::list<std::string> tokens = split(line, ',', "[", "]");
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    // copy to dom variable
    dom->variables[var_num] = (char *)(malloc(it->length() + 1));
    strcpy(dom->variables[var_num], it->c_str());
    var_num++;
  }
  dom->var_num = var_num;
  // Then parse the domain part
  tokens = split(line, ';', "{", "}");
  int curr_stmt = 0;

  // For each stmt iterate:
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    int num_iter = 0;
    sscanf(it->c_str(), "S%d%*s", &curr_stmt);
    std::list<std::string> iters = split(*it, ',', "[", "]");
    std::list<std::string> constraints = split_by_str(*it, "and", ":", ";");
    stmtSpace *stmt = init_stmtSpace(curr_stmt, iters.size());
    for (auto nn : iters) {
      indexBound *bound = init_indexBound();
      bound->index = (char *)(malloc(nn.length() + 1));
      strcpy(bound->index, nn.c_str());
      stmt->ib[num_iter] = bound;
      stmt->names[num_iter] = bound->index;
      num_iter++;
    }
    stmt->ib_num = num_iter;

    // Parse the inequality (constraint part)
    for (auto c : constraints) {
      parse_inequality(c, stmt);
    }
    // Compensation for unfound upper/lower bound:
    for (int i = 0; i < stmt->ib_num; i++) {
      if (stmt->ib[i]->ub == NULL)  compensate(stmt, i, 1);
      else if (stmt->ib[i]->lb == NULL) compensate(stmt, i, 0);
    }
    dom->stmt[dom->stmt_num] = stmt;
    dom->stmt_num++;
  }
  status = 1;
  // Could iterate through the list till the end
  dom->stmt[dom->stmt_num + 1] = NULL;
  return status;
}

int parse_dwarf_calc_bound(char **unit, FILE *fp, domainSpace *dom, 
                           std::vector<std::pair<const char *, int>> &var_n_val) {
  int status = 0;
  int skip = 1;
  int found = 0;
  char buffer[BUFFER_SIZE];
  char target[32];
  char *to_write;
  const char *long_mode = "    <%*x>   DW_AT_name        : (indirect string, offset: 0x%*x): %s";  
  const char *short_mode = "    <%*x>   DW_AT_name        : %s";
  // The rule of dwarf:
  // One element starts with line which the buf[1] is "<"
  // Then the following line is the attribute, which DW_AT_name is the first attribute of the elem
  // If the DW_AT_name matches the variable name, we want to find the DW_AT_const_value 5 lines after
  while (fgets(buffer, sizeof(buffer), fp) != NULL){
    if (buffer[1] == '<') {
      // New element, can do more detail check
      if (strstr(buffer, "DW_TAG_variable") == NULL){
        skip = 1;
        continue;
      }
      skip = 0;
      continue;
    }
    if (skip) continue;
    // Check if the current line contains DW_AT_name
    if (strstr(buffer, "DW_AT_name") == NULL){
      skip = 1;
      continue;
    } else {
      // Check if the DW_AT_name matches the variable name
      if (strlen(buffer) > 50){
        // use long parse string mode
        sscanf(buffer, long_mode, target);
      } else {
        // use short parse string mode
        sscanf(buffer, short_mode, target);
      }
      // Check if the DW_AT_name matches any variable name
      for (int i = 0; i < dom->var_num; i++){
        if (!strcmp(dom->variables[i], target)){
          found = 1;
          to_write = (char *)(malloc(strlen(target) + 1));
          strcpy(to_write, target);
          for (int j = 0; j < 5; j++){
            fgets(buffer, sizeof(buffer), fp);
          }
          if (strstr(buffer, "DW_AT_const_value") != NULL){
            int val;
            sscanf(buffer, "    <%*x>   DW_AT_const_value : %d", &val);
            var_n_val.push_back(std::make_pair(to_write, val));
            break;
          }
          break;
        }
      }if (!found){
        skip = 1;
        continue;
      }
      // Else, a matched on is found, create an table elem to subsitute content
    }
  }
  status = 1;
  return status;
}

/*
 * Calculate the value of the variable
 * @param in const char *var: the variable name
 * @param in std::vector<std::pair<const char *, int>> var_n_val: the list of variable and its value
 * @return int: the "actual calculated" value of the variable
 */
int calc_eq(const char *var, std::vector<std::pair<const char *, int>> var_n_val) {
  // tokenize the var, make all elem to list, sepqrate by " "
  long int temp_val = 0;
  long int val = 0;
  char *endptr;
  std::list<std::string> tokens;
  std::string token;
  // WIP: This Line Is Not Safe!!!
  if (var == NULL) {
    std::cout << "Error: var is NULL" << std::endl;
    return -1;
  }
  std::string *parse_arget = new std::string(var);
  size_t pos = 0;
  while ((pos = parse_arget->find(" ")) != std::string::npos) {
    token = parse_arget->substr(0, pos);
    tokens.push_back(token);
    parse_arget->erase(0, pos + 1);
  }
  tokens.push_back(*parse_arget);
  //Dump the list
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    // temp_val = atoi(it->c_str());
    temp_val = strtol ( it->c_str() , &endptr , 10 ) ;
    if (*endptr != '\0') {
      // Two cases: operator or number
      // Operator
      if (!strcmp(it->c_str(), "+") || !strcmp(it->c_str(), "-")
          || !strcmp(it->c_str(), "*") || !strcmp(it->c_str(), "/")) {
        continue;
      } else {
        // Might have subsitution
        for (auto p : var_n_val) {
          if (!strcmp(p.first, it->c_str())) {
            std::cout << "substituting: " << it->c_str() << " to " << p.second << std::endl;
            temp_val = p.second;
            val += temp_val;
            break;
          }
        }
      }
    } else {
      val += temp_val;
    }
    temp_val = 0;
  }
  // std::cout << "val: " << val << std::endl;
  return val;

}

int calc_dom_bound(domainSpace *dom, std::vector<std::pair<const char *, int>> var_n_val) {
  // First dump all ib in dom
  #ifdef DEBUG
  for (int i = 0; i < dom->stmt_num; i++) {
    stmtSpace *stmt = dom->stmt[i];
    std::cout << "S" << stmt->stmt_no << std::endl;
    for (int j = 0; j < stmt->ib_num; j++) {
      indexBound *ib = stmt->ib[j];
      if (ib->lb != NULL)
      {std::cout << ib->lb ;
      //std::cout << "is_lt: " << dom->ib[i]->is_lt << std::endl;
      if (ib->is_lt) std::cout << " < ";
      else std::cout << " <= " ;}
      std::cout << ib->index ;
      // std::cout << "is_gt: " << dom->ib[i]->is_gt << std::endl;
      if (ib->ub != NULL)
      {if (ib->is_gt) std::cout << " < ";
      else std::cout << " <= " ;
      std::cout << ib->ub << std::endl;}
    }
  }
  #endif

  for (int i = 0; i < dom->stmt_num; i++) {
    stmtSpace *stmt = dom->stmt[i];
    for (int j = 0; j < stmt->ib_num; j++) {
      indexBound *ib = stmt->ib[j];
      ib->ub_val = calc_eq(ib->ub, var_n_val);
      if (ib->is_gt) ib->ub_val--;
      ib->lb_val = calc_eq(ib->lb, var_n_val);
      if (ib->is_lt) ib->lb_val++;
    }
  }

  return 1;
}


isl_bool construction(__isl_keep isl_schedule_node *node, void *upper){
  /* Construction Phase of extTree */
  extTree **upper_ptr = (extTree **)upper;
  extTree *parent = *upper_ptr;
  extTree *current = init_extTree(parent->dom, *upper_ptr);
  // Rewrite the ptr to the current node
  printf("parent:\t%p\n", parent);
  printf("current:\t%p\n", current);

  enum isl_schedule_node_type type;
  type = isl_schedule_node_get_type(node);
  switch (type) {
    case isl_schedule_node_error:
    /* Error, terminated. */
      return isl_bool_false;
      break;
    case isl_schedule_node_band:
      current->type = isl_schedule_node_band;
      printf("This is a isl_schedule_node_band\n");
      break;
    case isl_schedule_node_context:
      current->type = isl_schedule_node_context;
      printf("This is a isl_schedule_node_context\n");
      break;
    case isl_schedule_node_domain:
      current->type = isl_schedule_node_domain;
      printf("This is a isl_schedule_node_domain\n");
      break;
    case isl_schedule_node_expansion:
      current->type = isl_schedule_node_expansion;
      printf("This is a isl_schedule_node_expansion\n");
      break;
    case isl_schedule_node_extension:
      current->type = isl_schedule_node_extension;
      printf("This is a isl_schedule_node_extension\n");
      break;
    case isl_schedule_node_filter:
      current->type = isl_schedule_node_filter;
      // Is a hint follow by the sequence node
      parent->child_num++;
      parent->children[parent->child_num] = current;
      printf("This is a isl_schedule_node_filter\n");
      break;
    case isl_schedule_node_leaf:
      current->type = isl_schedule_node_leaf;
      // Shall back to the sequence where it from
      free(current);
      while (parent->type != isl_schedule_node_sequence) {
        // Child Starts at 1
        parent = parent->parent;
      }
      current = parent;
      printf("This is a isl_schedule_node_leaf\n");
      break;
    case isl_schedule_node_guard:
      current->type = isl_schedule_node_guard;
      printf("This is a isl_schedule_node_guard\n");
      break;
    case isl_schedule_node_mark:
      current->type = isl_schedule_node_mark;
      printf("This is a isl_schedule_node_mark\n");
      break;
    case isl_schedule_node_sequence:
      current->type = isl_schedule_node_sequence;
      printf("This is a isl_schedule_node_sequence\n");
      break;
    case isl_schedule_node_set:
      current->type = isl_schedule_node_set;
      printf("This is a isl_schedule_node_set\n");
      break;
  }

  *upper_ptr = current;

  if (isl_schedule_node_get_type(node) != isl_schedule_node_leaf)
    return isl_bool_true;

	return isl_bool_false;
}

/*
 * Program initialization
 * argv[1]: the path to the binary
 * argv[2]: ppcg launch path
 */
int main(int argc, char *argv[]) {
  // initialize 10 ptr to store ppcg call path
  prog_path = argv[1];
  ppcg_launch = argv[2];

  FILE *fp;
  char cmd[BUFFER_SIZE];
  snprintf(cmd,BUFFER_SIZE-1, "readelf --debug-dump=info %s", prog_path);
  fp = popen(cmd, "r");
  if (fp == NULL) {
      printf("Failed to run command\n");
      exit(1);
  }

  // Same size as sched
  char *ret = (char *)(malloc(BUFFER_SIZE*sizeof(char) / 4));
  char **unit = (char **)(malloc(10 * sizeof(char *)));
  int compilation_unit = parse_dwarf(unit, fp);
  #ifdef DEBUG
  if (compilation_unit == 0) {
      printf("No DW_AT_name and DW_AT_comp_dir found\n");
  } else {
    // DEBUG
      printf("There are %d compilation unit\n", compilation_unit);
      for (int i = 0; i < compilation_unit; i++) {
          printf("%s\n", unit[i]);
      }
  }
  #endif
  int arg_count = get_computed_sched_from_ppcg(unit, ret, compilation_unit);

  if(!ret){
    printf("Error: ppcg call failed\n");
    return 1;
  }

  #ifdef DEBUG
  printf("The schedule is at %s\n", ret);
  #endif

  // Launch PPCG, get computed schedule, and reload it to the program
  // We may extract this part to another program later
  /*                  Extracttion                  */
  isl_ctx *ctx;
  isl_schedule *schedule;
	ctx = isl_ctx_alloc();

  FILE *file;
	file = fopen(ret, "r");
	if (!file) {
		fprintf(stderr, "Unable to open '%s' for reading\n", ret);
		return 1;
	}

  int status = 0;

  /* Part start to parse the domain from schedule tree domain */
  domainSpace *dom = init_domainSpace();
  status = extract_dom_from_sched(file, dom);
  
  // Reparse the dwarf to get the loop bound actual val
  // TODO
  // The fp is still open, we can reuse it, but move fd head to the beginning
  fp = popen(cmd, "r");
  std::vector<std::pair<const char *, int>> var_n_val;
  status = parse_dwarf_calc_bound(unit, fp, dom, var_n_val);
  // Dump the var_n_val
  for (auto p : var_n_val) {
    std::cout << p.first << " : " << p.second << "| ";
  } std::cout << std::endl;
  status = calc_dom_bound(dom, var_n_val);

  #ifdef DEBUG
  for (int i = 0; i < dom->stmt_num; i++) {
    stmtSpace *stmt = dom->stmt[i];
    std::cout << "S" << stmt->stmt_no << std::endl;
    for (int j = 0; j < stmt->ib_num; j++) {
      indexBound *ib = stmt->ib[j];
      std::cout << "lb: " << ib->lb << " / " << ib->lb_val 
                << " ub: " << ib->ub << " / " << ib->ub_val << std::endl;
    }
  }
  #endif

  // Construct the tree
  extTree *tree = (extTree *)(malloc(sizeof(extTree)));
  tree->dom = dom;
  tree->parent = NULL;
  tree->child_num = 0;
  tree->curr_child = 0;
  file = fopen(ret, "r");
	schedule = isl_schedule_read_from_file(ctx, file);
  extTree *type = (extTree *)(malloc(sizeof(extTree)));
  // Is the root node
  type->parent = NULL;
  type->dom = dom;
  isl_stat stat_ret = isl_schedule_foreach_schedule_node_top_down(schedule,
						&construction, &type);

  if (status == 1)
  {
    printf("Error: Unable to extract domain from the schedule\n");
    return 1;
  }
  // Create data structure for collecting address
  /* Parse data may look like this: 
    ##### (after 5 #s)
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[i, j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[i, -1 + j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[i, 1 + j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[1 + i, j] }
    read: [tsteps, n, b0, b1] -> { S1[t, i, j] -> A[-1 + i, j] }
    write: [tsteps, n, b0, b1] -> { S1[t, i, j] -> B[i, j] }
    write: [tsteps, n, b0, b1] -> { S2[t, i, j] -> A[i, j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[i, j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[i, -1 + j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[i, 1 + j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[1 + i, j] }
    read: [tsteps, n, b0, b1] -> { S2[t, i, j] -> B[-1 + i, j] }
  */
  int stmt = 1;
  // Read from the file after ##### ooccurs
  
  // Create pipe descriptors
  int pipe_fd[2];
  if (pipe(pipe_fd) == -1) {
    perror("pipe");
    exit(EXIT_FAILURE);
  }
  /*                  Extracttion                  */

  /**********************************************/
  /*                Call valgrind               */
  /**********************************************/

  // Fork a child process
  pid_t pid = fork();
  if (pid == -1) {
    perror("fork");
    exit(EXIT_FAILURE);
  }

  if (pid == 0) { // Child process (Program A)
    // Close the read end of the pipe
    close(pipe_fd[0]);

    // Redirect stdout to the pipe
  // It's magic, read from STDOUT and use VG_(message)(Vg_ClientMsg ... ) can send to the pipe
    dup2(pipe_fd[1], STDOUT_FILENO);

    // Close unused pipe descriptors
    close(pipe_fd[1]);

    // Change the working directory
    if (chdir("/home/dreyex/Documents/Research/PPT") == 0) {
      printf("Changed directory to /path/to/new_directory\n");
    } else {
      perror("chdir() error");
      return 1;
    }

    // Execute Program A
    // Since pass the program by arvg is sophisticated, we use execl with fixed path instead
    // What if then we have to run the batch of benchmarks?
    execl("/home/dreyex/Documents/Research/PPT/./vg-in-place", "vg-in-place",
          "--tool=cachegrind", "--instr-at-start=no", "--cache-sim=yes",
          "--D1=49152,12,64", "--I1=32768,8,64", "--L2=1310720,10,64", "-v", 
          "--log-fd=1", prog_path, NULL);
    perror("execl");
    exit(EXIT_FAILURE);
  } else { // Parent process (Program B)
    // Close the write end of the pipe
    int counter = 0;
    close(pipe_fd[1]);

    // Read from the pipe continuously
    char buffer[BUFFER_SIZE];
    ssize_t bytes_read;
    char cache[BUFFER_SIZE * 2]; // Double the buffer size for caching
    size_t cache_index = 0;
    int stop_receiving = 0;
    while (!stop_receiving &&
           (bytes_read = read(pipe_fd[0], buffer, BUFFER_SIZE)) > 0) {
      // Check if caching the data would exceed the buffer size
      if (cache_index + bytes_read >= sizeof(cache)) {
        fprintf(stderr, "Error: Buffer overflow\n");
        exit(EXIT_FAILURE);
      }

      // Cache the received data
      memcpy(cache + cache_index, buffer, bytes_read);
      cache_index += bytes_read;

      // Check if there is a complete line in the cache
      char *line_start = cache;
      char *line_end;
      char access;
      int line_no, size;
      long long int addr;
      /*
       * Recording the address, add thme into polyhedral model
       * Why we still need to record? 
       * Since sometimes the address is not that continuous as what we thought
       * physical address may change the page instead ( just an assumption )
       */
      while ((line_end = strchr(line_start, '\n')) != NULL) {
        // Null-terminate the line
        *line_end = '\0';

        // Check if the line starts with '%'
        if (line_start[0] == '*') {
          // Output the line
          // printf("detected at %s\n", line_start);
          sscanf(line_start, "**%*d** %c %d %llx %d", &access, &line_no, &addr, &size);

          // Output parsed values
          // printf("Access: %c, Line No: %d, Address: 0x%.10llx, Size: %d\n", access, line_no, addr, size);
    
          counter++;
        }

        // Check if the line starts with '#', then stop receiving
        if (line_start[0] == '#') {
          stop_receiving = 1;
          break;
        }

        // Move to the next line
        line_start = line_end + 1;
      }

      // Move the remaining data to the beginning of the cache
      size_t remaining_bytes = cache_index - (line_start - cache);
      memmove(cache, line_start, remaining_bytes);
      cache_index = remaining_bytes;
    }
    printf("There are %d line of output to here\n", counter);

    // Close the read end of the pipe
    close(pipe_fd[0]);

    // Wait for the child process to finish
    int status;
    waitpid(pid, &status, 0);
  }

  // Free the array of ptr
  for (int i = 0; i < compilation_unit; i++) {
    free(unit[i]);
  }
  free(unit);
	fclose(file);
  isl_schedule_free(schedule);
  isl_ctx_free(ctx);
  free(ret);
  return 0;
}
