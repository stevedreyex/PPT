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

typedef struct {
  /* name of the loop index from S[ x, x, x ... ] */
  char *index;
  /* May be less than or equal less than. */
  int is_lt;
  /* May be greater than or equal greater than. */
  int is_gt;
  char *ub;
  char *lb;
  int ub_val;
  int lb_val;
} indexBound;

typedef struct  {
  /* Number of undetermined vars */
  int n_num;
  /* Number of indexBound, also the number of stmts (in dom) */
  int ib_num;
  /* the [x, x, x, ...] -> { ... }, the x part, vars for inequality */
  char **variables;
  /* the [x, x, x, ...] -> { ... }, the ... part, the comstraint of each stmt */
  indexBound** bounds;
} stmtDomain;

#define BUFFER_SIZE 1024 // Increased buffer size

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
  
  snprintf(ppcg_call, BUFFER_SIZE-1, "%s %s --save-schedule=%s", ppcg_launch, ppcg_args, sched);
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

inline void parse_inequality(const std::string &s, stmtDomain dom){
  std::string tok = "<";
  int occurrences = 0;
  size_t pos = 0;
  int index_var;
  // Find which index this inequality is for
  for (int i = 0; i < dom.n_num; i++) {
    if (s.find(dom.variables[i]) != std::string::npos) {
      // This is the index
      index_var = i;
      break;
    }
  }

  // Find which inequality it is (2 or 3 elements?)
  while ((pos = s.find(tok, pos )) != std::string::npos) {
          ++ occurrences;
          pos += tok.length();
  }


  if (occurrences == 2) {
    // Find contents from initial to the first "<"
    size_t pos = s.find("<");
    // Start from 1, bypass the space
    std::string elem = s.substr(1, pos-1);
    dom.bounds[index_var]->lb = (char *)(malloc(elem.length() + 1));
    strcpy(dom.bounds[index_var]->lb, elem.c_str());
    // If the next char is "=", then it's less than or equal
    if (s[pos + 1] == '=') 
      dom.bounds[index_var]->is_lt = 0;
    else
      dom.bounds[index_var]->is_lt = 1;
    // Find contents from the second "<" to the end 
    pos = s.find("<", pos + 1);
    if (s[pos + 1] == '=') {
      dom.bounds[index_var]->is_gt = 0;
      // Bypass the "="
      pos++;
    }
    else
      dom.bounds[index_var]->is_gt = 1;
    // Bypass the " "
    pos++;
    elem = s.substr(pos + 1, s.length() - pos - 1);
    dom.bounds[index_var]->ub = (char *)(malloc(elem.length() + 1));
    std::cout << "elem: " << elem << std::endl;
    strcpy(dom.bounds[index_var]->ub, elem.c_str());
    // If the next char is "=", then it's less than or equal
  } 
  // else (occurrence = 1 Unimplemented)
}

/*
 * Extract the domain each statement from the schedule
 * @param in FILE *file: the file to extract the domain from
 * @param out stmtDomain *dom: the domain of each statement
 */
int extract_dom_from_sched(FILE *file, stmtDomain *dom) {
  char line[BUFFER_SIZE];
  int stmt = 0;
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
    dom->variables[stmt] = (char *)(malloc(it->length() + 1));
    strcpy(dom->variables[stmt], it->c_str());
    stmt++;
  }
  dom->n_num = stmt;
  // Then parse the domain part
  tokens = split(line, ';', "{", "}");
  int num_iter = 0;

  // std::cout << "domain: " << token << std::endl;
  // list dump
  for (std::list<std::string>::iterator it = tokens.begin(); it != tokens.end(); it++) {
    sscanf(it->c_str(), "S%d%*s", &stmt);
    std::cout << "S" << stmt << std::endl;
    std::list<std::string> iters = split(*it, ',', "[", "]");
    for (auto nn : iters) {
      indexBound *bound = (indexBound *)(malloc(sizeof(indexBound)));
      bound->index = (char *)(malloc(nn.length() + 1));
      dom->bounds[num_iter] = bound;
      strcpy(bound->index, nn.c_str());
      num_iter++;
    }
    iters.clear();
    iters = split_by_str(*it, "and", ":", ";");
    for (auto nn : iters) {
      parse_inequality(nn, *dom);
    }
    dom->ib_num++;
  }
  status = 1;
  dom->bounds[num_iter + 1] = NULL;
  return status;
}

int parse_dwarf_calc_bound(char **unit, FILE *fp, stmtDomain *dom, 
                           std::vector<std::pair<const char *, int>> &var_n_val) {
  int status = 0;
  int skip = 1;
  int found = 0;
  char buffer[BUFFER_SIZE];
  char target[32];
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
      for (int i = 0; i < dom->n_num; i++){
        if (!strcmp(dom->variables[i], target)){
          found = 1;
          std::cout << "found: " << target << std::endl;
          for (int j = 0; j < 5; j++){
            fgets(buffer, sizeof(buffer), fp);
          }
          if (strstr(buffer, "DW_AT_const_value") != NULL){
            int val;
            sscanf(buffer, "    <%*x>   DW_AT_const_value : %d", &val);
            var_n_val.push_back(std::make_pair(target, val));
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
    std::cout << buffer;
  }
  status = 1;
  return status;
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
  stmtDomain *dom = (stmtDomain *)(malloc(sizeof(stmtDomain)));
  dom->n_num = 0;
  dom->ib_num = 0;
  dom->bounds = (indexBound **)(malloc(10 * sizeof(indexBound *)));
  dom->variables = (char **)(malloc(10 * sizeof(char *)));
  status = extract_dom_from_sched(file, dom);
  
  // Reparse the dwarf to get the loop bound actual val
  // TODO
  // The fp is still open, we can reuse it, but move fd head to the beginning
  fp = popen(cmd, "r");
  std::vector<std::pair<const char *, int>> var_n_val;
  status = parse_dwarf_calc_bound(unit, fp, dom, var_n_val);
  if (status == 1)
  {
    printf("Error: Unable to extract domain from the schedule\n");
    return 1;
  }

	schedule = isl_schedule_read_from_file(ctx, file);
  #ifdef DEBUG
  isl_schedule_dump(schedule);
  #endif

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
