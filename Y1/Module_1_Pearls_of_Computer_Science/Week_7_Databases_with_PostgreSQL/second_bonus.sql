-- a)
SELECT srs.courses.course 
FROM srs.courses
LEFT JOIN srs.education
ON srs.courses.course_code = srs.education.course_code
WHERE srs.education.teacher_id IS NULL
INTERSECT
SELECT srs.courses.course 
FROM srs.courses
LEFT JOIN srs.grades
ON srs.courses.course_code = srs.grades.course_code
WHERE srs.grades.student_id IS NULL;

-- b)
SELECT 
  srs.grades.student_id, 
  srs.grades.student, 
  srs.grades.course, 
  MAX(srs.grades.grade) AS final_grade 
FROM srs.grades 
GROUP BY 
  srs.grades.student_id, 
  srs.grades.course, 
  srs.grades.student 
HAVING MAX(srs.grades.grade) < 6
ORDER BY srs.grades.student;

-- c)
SELECT 
  final_data.year, 
  final_data.course, 
  final_data.average_grade, 
  final_data.teacher
FROM (
  SELECT
    srs.education.year,
    srs.grades.course, 
    AVG(srs.grades.grade) AS average_grade,
    srs.education.teacher
  FROM srs.grades
  JOIN srs.education
  ON srs.grades.course_code = srs.education.course_code
  GROUP BY 
    srs.education.year,
    srs.grades.course, 
    srs.education.teacher
) AS final_data
JOIN (
  SELECT
    year,
    MIN(average_grade) AS min_average_grade
  FROM (
    SELECT
      srs.education.year,
      AVG(srs.grades.grade) AS average_grade
    FROM srs.grades
    JOIN srs.education
    ON srs.grades.course_code = srs.education.course_code
    GROUP BY 
      srs.education.year,
      srs.grades.course
  ) AS avg_grades_per_course
  GROUP BY year
) AS min_avg_grades_per_year
ON final_data.year = min_avg_grades_per_year.year
AND final_data.average_grade = min_avg_grades_per_year.min_average_grade
ORDER BY final_data.year;

-- d)
SELECT 
  srs.education.year,
  srs.education.teacher,
  srs.education.course,
  srs.education.course_code
FROM srs.education
JOIN (
  SELECT 
    year,
    teacher,
    COUNT(course_code) AS course_count
  FROM srs.education
  GROUP BY
    year,
    teacher
  HAVING COUNT(course_code) = 1
) AS one_course_per_year
ON 
  srs.education.year = one_course_per_year.year
  AND srs.education.teacher = one_course_per_year.teacher
ORDER BY 
  srs.education.year, 
  srs.education.teacher;

-- e)
SELECT student_id, 
       student, 
       study
FROM (
    SELECT g.student_id, 
           g.student, 
           e.study, 
           COUNT(e.study) AS study_count,
           RANK() OVER (PARTITION BY g.student_id ORDER BY COUNT(e.study) DESC) AS rank -- for additional reference the rank 1 is the highest so we need it to represent the most relevant study
    FROM srs.grades g 
    JOIN srs.education e ON g.course_code = e.course_code 
                        AND g.year = e.year 
                        AND g.quarter = e.quarter
    GROUP BY g.student_id, g.student, e.study
) AS ranked_studies
WHERE rank = 1
ORDER BY student_id;

