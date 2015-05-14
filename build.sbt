name := "adtsolver-standalone"

version := "0.1"

scalaVersion := "2.10.4"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" % "test"

libraryDependencies += "junit" % "junit" % "4.10" % "test"

testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-oF")