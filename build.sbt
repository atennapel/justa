val scala3Version = "3.7.4"

lazy val root = project
  .in(file("."))
  .settings(
    name := "justa",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    scalacOptions ++= Seq(
      "-Wunused:imports",
      "-Xfatal-warnings",
      "-explain-cyclic",
      "-language:strictEquality"
    ),
    javacOptions ++= Seq("-source", "25", "-target", "25")
  )
