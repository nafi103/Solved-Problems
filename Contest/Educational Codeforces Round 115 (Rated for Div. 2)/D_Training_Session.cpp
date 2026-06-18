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
 const int N = 2e5;
pair<int, int> problem[N];
int ca[N + 1], cb[N + 1];
 void solve()
{
    int n, bad = 0;
    cin >> n;
    for (int i = 1; i <= n; i++)
    {
        ca[i] = 0;
        cb[i] = 0;
    }
    for (int i = 0; i < n; i++)
    {
        auto &[a, b] = problem[i];
        cin >> a >> b;
        ca[a]++;
        cb[b]++;
    }
    for (int i = 0; i < n; i++)
    {
        auto &[a, b] = problem[i];
        int x = ca[a], y = cb[b];
        bad += (x - 1) * (y - 1);
    }
    cout << (n * (n - 1) * (n - 2)) / 6 - bad << endl;
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