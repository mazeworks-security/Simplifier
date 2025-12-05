using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Mba.Simplifier.DSL
{
    class CodeBuilder
    {
        private string indent = String.Empty;

        private StringBuilder builder;

        public CodeBuilder()
        {
            builder = new StringBuilder();
        }

        public CodeBuilder(StringBuilder sb)
        {
            builder = sb;
        }

        public void Indent(int count = 1)
        {
            for (int i = 0; i < count; i++)
                indent += "    ";
        }

        public void Outdent(int count = 1)
        {
            for (int i = 0; i < count; i++)
                indent = indent.Substring(0, indent.Length - 4);
        }

        public void AppendLine(string text)
        {
            builder.AppendLine(indent + text);
        }

        public void Append(string text)
        {
            builder.Append(indent + text);
        }

        public void Append(string text, params object[] args)
        {
            builder.AppendFormat(indent + text, args);
        }

        public override string ToString()
        {
            return builder.ToString();
        }
    }
}
