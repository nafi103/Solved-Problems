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

void solve()
{
    int n, ans = 0;
    cin >> n;
    vector<pair<int, int>> range(n);
    for (auto &[f, s] : range)
    {
        cin >> f >> s;
        ans += s - f;
    }
    sort(all(range), [&](pair<int, int> &a, pair<int, int> &b)
         {
        if(a.first+a.second != b.first+b.second)
            return a.first + a.second < b.first + b.second;
        return a.first < b.first; });
    if (n % 2 == 0)
    {
        for (int i = 0; i < n; i++)
        {
            if (i < n / 2)
                ans -= range[i].first;
            else
                ans += range[i].second;
        }
        cout << ans << endl;
        return;
    }
    for (int i = 1; i < n; i++)
    {
        if (i <= n / 2)
            ans -= range[i].first;
        else
            ans += range[i].second;
    }
    int mx_ans = ans;
    for (int i = 1; i <= n / 2; i++)
    {
        mx_ans = max(mx_ans, ans);
        ans += range[i].first;
        ans -= range[i-1].first;
    }
    for (int i = n / 2 + 1; i < n; i++){
        mx_ans = max(mx_ans, ans);
        ans -= range[i].second;
        ans += range[i - 1].second;
    }
    mx_ans = max(mx_ans, ans);
    cout << mx_ans << endl;
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