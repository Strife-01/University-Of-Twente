-- This bonus contains both first one and data integrity

-- Drop all tables for debugging purposes
DROP TABLE IF EXISTS module CASCADE;
DROP TABLE IF EXISTS final_grade CASCADE;
DROP TABLE IF EXISTS teaches CASCADE;  
DROP TABLE IF EXISTS course_edition CASCADE;
DROP TABLE IF EXISTS student CASCADE;
DROP TABLE IF EXISTS teacher CASCADE;
DROP TABLE IF EXISTS course CASCADE;
DROP TABLE IF EXISTS study CASCADE;
DROP TABLE IF EXISTS pearl_test_database CASCADE;
DROP TABLE IF EXISTS test CASCADE;
DROP TABLE IF EXISTS teaching_assistant_for CASCADE;
DROP TABLE IF EXISTS teaching_assistant CASCADE;

-- Design the schema of the database
CREATE TABLE study (
  study_code VARCHAR(255) UNIQUE NOT NULL,
  study VARCHAR(255) NOT NULL PRIMARY KEY
);

CREATE TABLE course (
  course_code INTEGER UNIQUE NOT NULL PRIMARY KEY,
  course TEXT NOT NULL,
  study VARCHAR(255) NOT NULL,
  description TEXT NOT NULL,
  ects SMALLINT DEFAULT 5,
  FOREIGN KEY(study) REFERENCES study(study)
);

CREATE TABLE module (
  course_code INTEGER UNIQUE NOT NULL PRIMARY KEY,
  nr_test SMALLINT DEFAULT 1,
  ects SMALLINT DEFAULT 15,
  FOREIGN KEY(course_code) REFERENCES course(course_code)
);

CREATE TABLE student (
  student_id INTEGER UNIQUE NOT NULL PRIMARY KEY,
  study VARCHAR(255) NOT NULL,
  student TEXT NOT NULL,
  FOREIGN KEY(study) REFERENCES study(study)
);

CREATE TABLE teacher (
  teacher_id INTEGER UNIQUE NOT NULL PRIMARY KEY,
  teacher TEXT NOT NULL,
  start_date DATE,
  end_date DATE
);

CREATE TABLE teaching_assistant (
  teacher_id INTEGER UNIQUE NOT NULL,
  FOREIGN KEY(teacher_id) REFERENCES teacher(teacher_id)
) INHERITS (student);

CREATE TABLE course_edition (
  year SMALLINT NOT NULL,
  quarter SMALLINT NOT NULL,
  course_code INTEGER NOT NULL,
  main_teacher INTEGER NOT NULL,
  PRIMARY KEY (course_code, year, quarter, main_teacher),
  UNIQUE (course_code, year, quarter),
  FOREIGN KEY (course_code) REFERENCES course(course_code),
  FOREIGN KEY (main_teacher) REFERENCES teacher(teacher_id)
);

CREATE TABLE teaching_assistant_for (
  student_id INTEGER NOT NULL,
  year SMALLINT NOT NULL,
  quarter SMALLINT NOT NULL,
  course_code INTEGER NOT NULL,
  main_teacher INTEGER NOT NULL,
  FOREIGN KEY(student_id) REFERENCES student(student_id),
  FOREIGN KEY(course_code, year, quarter, main_teacher) REFERENCES course_edition(course_code, year, quarter, main_teacher)
);

CREATE TABLE test (
  test_id SERIAL PRIMARY KEY,
  test_name TEXT,
  year SMALLINT NOT NULL,
  quarter SMALLINT NOT NULL,
  course_code INTEGER NOT NULL,
  main_teacher INTEGER NOT NULL,
  FOREIGN KEY(course_code, year, quarter, main_teacher) REFERENCES course_edition(course_code, year, quarter, main_teacher)
);

CREATE TABLE teaches (
  teacher_id INTEGER NOT NULL,
  course_code INTEGER NOT NULL,
  year SMALLINT NOT NULL,
  quarter SMALLINT NOT NULL,
  PRIMARY KEY (teacher_id, course_code, year, quarter),
  FOREIGN KEY(teacher_id) REFERENCES teacher(teacher_id),
  FOREIGN KEY(course_code, year, quarter) REFERENCES course_edition(course_code, year, quarter)
);

CREATE TABLE final_grade (
  grade SMALLINT NOT NULL CHECK (grade >= 0),
  course_code INTEGER NOT NULL,
  student_id INTEGER NOT NULL,
  FOREIGN KEY(course_code) REFERENCES course(course_code),
  FOREIGN KEY(student_id) REFERENCES student(student_id),
  PRIMARY KEY (course_code, student_id)
);

CREATE TABLE pearl_test_database (
  pearl_test_database_id SERIAL,
  grade SMALLINT NOT NULL CHECK (grade >= 0) ,
  course_code INTEGER NOT NULL,
  student_id INTEGER NOT NULL,
  test_id INTEGER,
  FOREIGN KEY(course_code) REFERENCES course(course_code),
  FOREIGN KEY(student_id) REFERENCES student(student_id),
  FOREIGN KEY(test_id) REFERENCES test(test_id)
);

-- Insert unique studies into study table
INSERT INTO study (study_code, study) -- We don't have study names so we just duplicate the study name in study code
SELECT DISTINCT study, study 
FROM education
ON CONFLICT (study_code) DO NOTHING; -- Ignore if the study already exists

-- Insert unique courses into course table
INSERT INTO course (course_code, course, study, description)
SELECT DISTINCT education.course_code, education.course, education.study, courses.description 
FROM education 
JOIN courses ON education.course_code = courses.course_code 
ON CONFLICT (course_code) DO NOTHING; -- Ignore if the course already exists

-- Insert unique students into student table
INSERT INTO student (student_id, study, student)
SELECT DISTINCT grades.student_id, education.study, grades.student 
FROM grades 
JOIN education ON grades.course_code = education.course_code 
ON CONFLICT (student_id) DO NOTHING; -- Ignore if the student already exists | In case there are students with more than 1 study this will cause the conflict so it will be droppet alltogether

-- Insert unique teachers into teacher table
INSERT INTO teacher (teacher_id, teacher, start_date, end_date)
SELECT DISTINCT teacher_id, teacher, 
    MIN(make_date(year, quarter * 3 - 2, 1))::date, 
    MAX(make_date(year, quarter * 3 - 2, 1))::date 
FROM education 
GROUP BY teacher_id, teacher
ON CONFLICT (teacher_id) DO NOTHING; -- Ignore if the teacher already exists

-- Ensure only valid course_code entries are inserted into course_edition
INSERT INTO course_edition (year, quarter, course_code, main_teacher)
SELECT DISTINCT year, quarter, course_code, teacher_id 
FROM education 
WHERE course_code IN (SELECT course_code FROM course)  -- Only valid course codes
GROUP BY year, quarter, course_code, teacher_id;


-- Insert into teaches table
INSERT INTO teaches (teacher_id, course_code, year, quarter)
SELECT DISTINCT teacher_id, course_code, year, quarter
FROM education
WHERE course_code IN (SELECT course_code FROM course)
GROUP BY teacher_id, course_code, year, quarter;

-- Insert final grades
INSERT INTO final_grade (grade, course_code, student_id)
SELECT DISTINCT MAX(grade), course_code, student_id 
FROM grades 
GROUP BY course_code, student_id;

-- Insert grades in the database
INSERT INTO pearl_test_database (grade, course_code, student_id)
SELECT DISTINCT grade, course_code, student_id 
FROM grades;

/*
-- Check for existing teachers
SELECT * 
FROM teacher 
WHERE teacher_id IN (1019819, 1010191);  -- Check both existing teachers
*/

-- Insert missing teachers (including the five students as teachers)
INSERT INTO teacher (teacher_id, teacher, start_date, end_date)
VALUES 
  (1019819, 'John Doe', '2024-01-01', NULL),  -- Add student 1019819 as a teacher
  (1010191, 'Jane Smith', '2024-01-01', NULL),  -- Add student 1010191 as a teacher
  (1011856, 'Student Name 1', '2024-01-01', NULL),  -- Add student 1011856 as a teacher
  (1012192, 'Student Name 2', '2024-01-01', NULL),  -- Add student 1012192 as a teacher
  (1015849, 'Student Name 3', '2024-01-01', NULL)   -- Add student 1015849 as a teacher
ON CONFLICT (teacher_id) DO NOTHING;  -- Prevent duplicates

-- Insert into course_edition
INSERT INTO course_edition (year, quarter, course_code, main_teacher)
VALUES 
  (2024, 1, 121021, 1019819),  -- Insert for the first course with John Doe
  (2024, 1, 122829, 1010191);  -- Insert for the second course with Jane Smith

-- Insert teaching assistantships
INSERT INTO teaching_assistant_for (student_id, year, quarter, course_code, main_teacher)
VALUES 
  (1011856, 2024, 1, 121021, 1019819),  -- Student 1011856 as teaching assistant for course 121021
  (1012192, 2024, 1, 121021, 1019819),  -- Student 1012192 as teaching assistant for course 121021
  (1015849, 2024, 1, 122829, 1010191),  -- Student 1015849 as teaching assistant for course 122829
  (1019819, 2024, 1, 122829, 1010191),  -- Existing teacher 1019819 also as TA for course 122829 (adjust if needed)
  (1010191, 2024, 1, 121021, 1019819);  -- Existing teacher 1010191 also as TA for course 121021 (adjust if needed)

  -- Step 1: Insert two modules into the module table
INSERT INTO module (course_code, nr_test, ects)
VALUES 
  (121021, 1, 15),  -- Module for course 121021 with 1 test and 15 ECTS
  (122829, 1, 15)   -- Module for course 122829 with 1 test and 15 ECTS
