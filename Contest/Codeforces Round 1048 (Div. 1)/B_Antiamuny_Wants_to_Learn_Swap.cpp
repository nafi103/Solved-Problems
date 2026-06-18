#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 struct Segment_Tree
{
    vector<int> t, v;
     Segment_Tree(int n)
    {
        v.clear();
        t.assign(4 * n, inf);
    }
     Segment_Tree(int n, vector<int> &_v)
    {
        v = _v;
        t.resize(4 * n);
        build(1, 1, n);
    }
     void build(int node, int b, int e)
    {
        if (b == e)
        {
            t[node] = v[b];
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        t[node] = min(t[left], t[right]);
    }
     void update(int node, int b, int e, int &idx, int &value)
    {
        if (b == e)
        {
            t[node] = value;
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        if (idx <= mid)
            update(left, b, mid, idx, value);
        else
            update(right, mid + 1, e, idx, value);
        t[node] = min(t[left], t[right]);
    }
     int query(int node, int b, int e, int l, int r)
    {
        if (b > r or e < l)
            return inf;
        if (b >= l and e <= r)
            return t[node];
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        return min(query(left, b, mid, l, r), query(right, mid + 1, e, l, r));
    }
};
 void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> v(n + 1), immediate(n + 1), final_arr(n + 1);
    for (int i = 1; i <= n; i++)
    {
        cin >> v[i];
    }
    stack<int> st;
    for (int i = n; i >= 1; i--)
    {
        while (!st.empty() and v[st.top()] > v[i])
            st.pop();
        immediate[i] = (st.empty() ? inf : st.top());
        st.push(i);
    }
     Segment_Tree st1(n);
    for (int i = n; i >= 1; i--)
    {
        int &x = v[i];
        final_arr[i] = st1.query(1, 1, n, 1, x - 1);
        st1.update(1, 1, n, x, immediate[i]);
    }
     Segment_Tree st2(n, final_arr);
    while (q--)
    {
        int l, r;
        cin >> l >> r;
        int ans = st2.query(1, 1, n, l, r);
        cout << (ans <= r ? "NO" : "YES") << endl;
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}