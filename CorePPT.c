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

struct options {
	struct isl_options	*isl;
	struct pet_options	*pet;
	char			*input;
};

ISL_ARGS_START(struct options, options_args)
ISL_ARG_CHILD(struct options, isl, "isl", &isl_options_args, "isl options")
ISL_ARG_CHILD(struct options, pet, NULL, &pet_options_args, "pet options")
ISL_ARG_ARG(struct options, input, "input", NULL)
ISL_ARGS_END

ISL_ARG_DEF(options, struct options, options_args)

char *prog_path;    // argv[1]
char *ppcg_launch;  // argv[2]

#define BUFFER_SIZE 1024 // Increased buffer size

/*
 * Parse the DWARF information from the binary
 * @param out char **unit: the array of compiled source path
 * @return int: number of compilation unit
 */
int parse_dwarf(char **unit){

  FILE *fp;
  int compilation_unit = 0;
  char path[1035];
  char prev_line[1035] = "";
  
  //init the array, assume there's only 10 compilation unit
  for (int i = 0; i < 10; i++) {
    unit[i] = NULL;
  }

  // Open the command for reading
  char cmd[BUFFER_SIZE];
  snprintf(cmd,BUFFER_SIZE-1, "readelf --debug-dump=info %s", prog_path);
  fp = popen(cmd, "r");
  if (fp == NULL) {
      printf("Failed to run command\n");
      exit(1);
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
                unit[compilation_unit] = malloc(strlen(colon_pos_name) + 1);
                // copy content and discard contents after 
                char *last_slash = strrchr(colon_pos_name, '/');
                if (last_slash != NULL) {
                    //remove last_slash in colon_pos_name
                    *last_slash = '\0';
                } 
                strcpy(unit[compilation_unit], colon_pos_name);
            // Where tha main at
            } else {
                unit[compilation_unit] = malloc(strlen(colon_pos_name) + 1);
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
  char *incl = "-I";

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
    strncpy(ret, sched, strlen(sched));
  }
  pclose(fp);

  return arg_count;
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
  // Same size as sched
  char *ret = malloc(BUFFER_SIZE*sizeof(char) / 4);
  char **unit = malloc(10 * sizeof(char *));
  int compilation_unit = parse_dwarf(unit);
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

  isl_ctx *ctx;
	struct pet_scop *scop;
	struct options *options;
  isl_schedule *schedule;
	options = options_new_with_defaults();
	ctx = isl_ctx_alloc_with_options(&options_args, options);
	// arg_count = options_parse(options, arg_count, arg_list, ISL_ARG_ALL);

	// scop = pet_scop_extract_from_C_source(ctx, options->input, NULL);
  // schedule = pet_scop_get_schedule(scop);

  FILE *file;
	file = fopen(ret, "r");
	if (!file) {
		fprintf(stderr, "Unable to open '%s' for reading\n", ret);
		return 1;
	}
	schedule = isl_schedule_read_from_file(ctx, file);
  // isl_schedule_dump(schedule);

  // Create pipe descriptors
  int pipe_fd[2];
  if (pipe(pipe_fd) == -1) {
    perror("pipe");
    exit(EXIT_FAILURE);
  }

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
          "--log-fd=1", "/home/dreyex/use_this/jacobi-2d", NULL);
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
