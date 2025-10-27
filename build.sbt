val scala3Version = "3.7.3"

lazy val root = project
  .in(file("."))
  .settings(
    name := "justa",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    scalacOptions ++= Seq(
      "-deprecation",
      "-Wunused:imports",
      "-Xfatal-warnings",
      "-explain-cyclic"
    )
  )
