-- Drop all tables for debugging purposes
DROP TABLE IF EXISTS final_grade;
DROP TABLE IF EXISTS teaches;  
DROP TABLE IF EXISTS course_edition;
DROP TABLE IF EXISTS student;
DROP TABLE IF EXISTS teacher;
DROP TABLE IF EXISTS course;
DROP TABLE IF EXISTS study;

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
  grade SMALLINT NOT NULL,
  course_code INTEGER NOT NULL,
  student_id INTEGER NOT NULL,
  FOREIGN KEY(course_code) REFERENCES course(course_code),
  FOREIGN KEY(student_id) REFERENCES student(student_id),
  PRIMARY KEY (course_code, student_id)
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

-- 7.5
-- a)
SELECT DISTINCT student.student FROM student WHERE student.study = 'BIT';
-- b)
SELECT DISTINCT course.course FROM course_edition, course WHERE course_edition.course_code = course.course_code AND course_edition.main_teacher = (SELECT teacher_id FROM teacher where teacher ILIKE '%Keulen%');
-- c)
SELECT DISTINCT teacher FROM teacher WHERE teacher_id IN (SELECT main_teacher FROM course_edition, course WHERE course.course_code = course_edition.course_code AND course.description ILIKE '%databases%');

-- 7.6
-- a)
UPDATE teacher SET end_date = '2003-12-31' WHERE teacher = 'HIEMSTRA DR IR D';
-- b)
INSERT INTO course_edition (year, quarter, course_code, main_teacher)
SELECT DISTINCT 2004 AS year, quarter, course_code, main_teacher
FROM course_edition
WHERE year = 2003 AND quarter = 4;
-- c)
INSERT INTO teacher (teacher_id, teacher, start_date, end_date)
VALUES ((SELECT MAX(teacher_id) + 1 FROM teacher), 'HUISMAN PROF DR M', '2004-01-01', '2024-12-31');

INSERT INTO course_edition (year, quarter, course_code, main_teacher)
SELECT DISTINCT 2004 AS year, quarter, course_code, (SELECT teacher_id FROM teacher WHERE teacher ILIKE '%HUISMAN%') AS main_teacher
FROM course_edition
WHERE year = 2003 AND main_teacher = (SELECT teacher_id FROM teacher WHERE teacher ILIKE '%BRINKSMA%');

