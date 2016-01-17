import org.sbtidea.SbtIdeaPlugin._
import sbtassembly.Plugin.AssemblyKeys._


name := "simplifier"

version := "1.0.0"

scalaVersion. := ("2.11.2")

libraryDependencies ++= Seq(
  "org.antlr" % "antlr4" % "4.3",
  "org.specs2" %% "specs2-core" % "2.4.14" % "test",
  "org.scalatest" % "scalatest_2.11" % "2.2.1" % "test"
)

scalacOptions ++= Seq(
  "-unchecked",
  "-deprecation",
  "-encoding",
  "utf8",
  "-feature"
)

javacOptions += "-proc:none"

antlr4Settings

antlr4GenListener in Antlr4 := false

antlr4GenVisitor in Antlr4 := true

antlr4PackageName in Antlr4 := Some("parser")

antlr4OutputDir in Antlr4 := (javaSource in Compile).value

assemblySettings

test in assembly := {}

jarName in assembly := "simplifier.jar"

mainClass in assembly := Some("Main")

ideaExcludeFolders ++= Seq(".idea_modules", ".idea", "target")
