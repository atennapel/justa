val scala3Version = "3.8.1"

lazy val root = project
  .in(file("."))
  .settings(
    name := "justa",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    scalacOptions ++= Seq(
      "-Wunused:imports",
      "-Werror",
      "-explain-cyclic",
      "-language:strictEquality",
      "-deprecation"
    ),
    javacOptions ++= Seq("-source", "25", "-target", "25")
  )
