#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#define BUFFER_SIZE 1024 // Increased buffer size

int main() {


  FILE *fp;
  int compilation_unit = 0;
  char path[1035];
  char prev_line[1035] = "";
  char **unit = malloc(10 * sizeof(char *));
  //init the array, assume there's only 10 compilation unit
  for (int i = 0; i < 10; i++) {
    unit[i] = NULL;
  }

  // Open the command for reading
  fp = popen("readelf --debug-dump=info /home/dreyex/use_this/jacobi-2d", "r");
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
        char *colon_pos_comp = strchr(path, ':');
        char *colon_pos_name = strchr(prev_line, ':');
        for (int i = 0; i < 2 && colon_pos_comp != NULL; i++) {
            colon_pos_comp = strchr(colon_pos_comp + 1, ':');
        }
        for (int i = 0; i < 2 && colon_pos_name != NULL; i++) {
            colon_pos_name = strchr(colon_pos_name + 1, ':');
        }
        colon_pos_comp += 2;
        colon_pos_name += 2;
        colon_pos_comp[strcspn(colon_pos_comp, "\n")] = '\0';
        colon_pos_name[strcspn(colon_pos_name, "\n")] = '\0';
        if (colon_pos_comp != NULL && colon_pos_name != NULL) {
            // Print the substring starting from the position after the third colon
            // printf("%s/%s\n", colon_pos_comp , colon_pos_name);
            // if the colon_pos_name starts with .., trim *.c from the path
            if (colon_pos_name[0] == '.' && colon_pos_name[1] == '.') {
                unit[compilation_unit] = malloc(strlen(colon_pos_comp) + strlen(colon_pos_name) + 2);
                strcpy(unit[compilation_unit], colon_pos_comp);
                strcat(unit[compilation_unit], "/");
                strncat(unit[compilation_unit], colon_pos_name, strlen(colon_pos_name) - 2);
            } else {
                unit[compilation_unit] = malloc(strlen(colon_pos_comp) + strlen(colon_pos_name) + 2);
                strcpy(unit[compilation_unit], colon_pos_comp);
                strcat(unit[compilation_unit], "/");
                strcat(unit[compilation_unit], colon_pos_name);
            }
            compilation_unit++;
        }
      }
      // Save the current line to prev_line
      strcpy(prev_line, path);
  }
  if (compilation_unit == 0) {
      printf("No DW_AT_name and DW_AT_comp_dir found\n");
  } else {
    // DEBUG
      printf("There are %d compilation unit\n", compilation_unit);
      for (int i = 0; i < compilation_unit; i++) {
          printf("%s\n", unit[i]);
      }
  }
  // Close the pipe
  pclose(fp);

  // Create pipe descriptors
  int pipe_fd[2];
  if (pipe(pipe_fd) == -1) {
    perror("pipe");
    exit(EXIT_FAILURE);
  }

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
          "-d", "--log-fd=1", "/home/dreyex/use_this/jacobi-2d", NULL);
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

  return 0;
}
