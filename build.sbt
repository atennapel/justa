val scala3Version = "3.4.2"

lazy val root = project
  .in(file("."))
  .settings(
    name := "justa",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    scalacOptions ++= Seq("-Wunused:imports", "-Xfatal-warnings"),
    libraryDependencies += "com.github.j-mie6" %% "parsley" % "4.5.2"
  )
