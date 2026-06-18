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
vector<int> pre(8000), curr(8000);

void solve()
{
    int n;
    cin >> n;
    vector<int> a(n), c(n);
    set<int> s;
    for (auto &x : a)
    {
        cin >> x;
        s.insert(x);
    }
    for (auto &x : c)
        cin >> x;
    if (n == 1)
    {
        cout << 0 << endl;
        return;
    }
    map<int, int> mp;
    int id = 0;
    for (auto &x : s)
    {
        mp[x] = id++;
    }
    for (auto &x : a)
        x = mp[x];
    for (int i = 0; i < id; i++)
    {
        if (a[0] == i)
            pre[i] = 0;
        else
            pre[i] = c[0];
    }
    for (int i = 1; i < n; i++)
    {
        for (int j = 0, mn = pre[0]; j < id; j++, mn = min(mn, pre[j]))
        {
            curr[j] = mn + (j == a[i] ? 0 : c[i]);
        }
        if (i < n - 1)
        {
            for (int j = 0; j < id; j++)
                pre[j] = curr[j];
        }
    }
    cout << *min_element(curr.begin(), curr.begin() + id) << endl;
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