val scala3Version = "3.7.1"

lazy val root = project
  .in(file("."))
  .settings(
    name := "justa",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    scalacOptions ++= Seq(
      "-Wunused:imports",
      "-Xfatal-warnings",
      "-explain-cyclic"
    ),
    libraryDependencies += "org.ow2.asm" % "asm" % "9.8",
    libraryDependencies += "org.ow2.asm" % "asm-commons" % "9.8"
  )
