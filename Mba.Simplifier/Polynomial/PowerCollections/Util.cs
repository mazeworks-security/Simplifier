//******************************
// Written by Peter Golde
// Copyright (c) 2004-2005, Wintellect
//
// Use and restribution of this code is subject to the license agreement 
// contained in the file "License.txt" accompanying this file.
//******************************

using System;
using System.Collections;
using System.Collections.Generic;

namespace Wintellect.PowerCollections
{
	/// <summary>
	/// A holder class for various internal utility functions that need to be shared.
	/// </summary>
    internal static class Util
    {
        /// <summary>
        /// Determine if a type is cloneable: either a value type or implementing
        /// ICloneable.
        /// </summary>
        /// <param name="type">Type to check.</param>
        /// <param name="isValue">Returns if the type is a value type, and does not implement ICloneable.</param>
        /// <returns>True if the type is cloneable.</returns>
        public static bool IsCloneableType(Type type, out bool isValue)
        {
            isValue = false;
#if PCL

            return false;
#else
            if (typeof(ICloneable).IsAssignableFrom(type)) {
                return true;
            }
            else if (type.IsValueType) {
                isValue = true;
                return true;
            }
            else
                return false;
#endif

        }

        /// <summary>
        /// Returns the simple name of the class, for use in exception messages. 
        /// </summary>
        /// <returns>The simple name of this class.</returns>
        public static string SimpleClassName(Type type)
        {
            string name = type.Name;

            // Just use the simple name.
            int index = name.IndexOfAny(new char[] { '<', '{', '`' });
            if (index >= 0)
                name = name.Substring(0, index);

            return name;
        }

        /// <summary>
        /// Wrap an enumerable so that clients can't get to the underlying 
        /// implementation via a down-cast.
        /// </summary>
#if !PCL
    [Serializable]
#endif
        class WrapEnumerable<T> : IEnumerable<T>
        {
            IEnumerable<T> wrapped;

            /// <summary>
            /// Create the wrapper around an enumerable.
            /// </summary>
            /// <param name="wrapped">IEnumerable to wrap.</param>
            public WrapEnumerable(IEnumerable<T> wrapped)
            {
                this.wrapped = wrapped;
            }

            public IEnumerator<T> GetEnumerator()
            {
                return wrapped.GetEnumerator();
            }

            IEnumerator IEnumerable.GetEnumerator()
            {
                return ((IEnumerable)wrapped).GetEnumerator();
            }
        }

        /// <summary>
        /// Wrap an enumerable so that clients can't get to the underlying
        /// implementation via a down-case
        /// </summary>
        /// <param name="wrapped">Enumerable to wrap.</param>
        /// <returns>A wrapper around the enumerable.</returns>
        public static IEnumerable<T> CreateEnumerableWrapper<T>(IEnumerable<T> wrapped)
        {
            return new WrapEnumerable<T>(wrapped);
        }

        /// <summary>
        /// Gets the hash code for an object using a comparer. Correctly handles
        /// null.
        /// </summary>
        /// <param name="item">Item to get hash code for. Can be null.</param>
        /// <param name="equalityComparer">The comparer to use.</param>
        /// <returns>The hash code for the item.</returns>
        public static int GetHashCode<T>(T item, IEqualityComparer<T> equalityComparer)
        {
            if (item == null)
                return 0x1786E23C;
            else
                return equalityComparer.GetHashCode(item);
        }

        /// <summary>
        /// Lookup table for <see cref="LogBase2"/>.
        /// </summary>
        /// <remarks>
        /// https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogDeBruijn
        /// </remarks>
        private static readonly int[] MultiplyDeBruijnBitPosition =
        {
            0, 9, 1, 10, 13, 21, 2, 29, 11, 14, 16, 18, 22, 25, 3, 30,
            8, 12, 20, 28, 15, 17, 24, 7, 19, 27, 23, 6, 26, 5, 4, 31
        };

        /// <summary>
        /// Gets the log-base-2 of a positive integer value.
        /// </summary>
        /// <param name="v">Value whose log-base-2 to calculate.</param>
        /// <returns>The log-base-2 of the value.</returns>
        /// <remarks>
        /// https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogDeBruijn
        /// </remarks>
        public static int LogBase2(uint v)
        {
            // first round down to one less than a power of 2
            v |= v >> 1;
            v |= v >> 2;
            v |= v >> 4;
            v |= v >> 8;
            v |= v >> 16;

            return MultiplyDeBruijnBitPosition[unchecked((uint)(v * 0x07C4ACDDUL)) >> 27];
        }
    }
}
