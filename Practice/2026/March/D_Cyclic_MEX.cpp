#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int n, mex = 0, sum = 0, ans = 0;
    cin >> n;
    vector<int> arr(2 * n), m(2 * n), s(n + 1, 0);
    for(int i = 0; i < 2 * n; i++){
        if(i < n)
            cin >> arr[i];
        else
            arr[i] = arr[i % n];
        s[arr[i]]++;
        while(s[mex])
            mex++;
        m[i] = mex;
    }
    deque<pair<int,int>> d;
    for(int i = 0; i < n; i++){
        if(d.empty() or d.back().first != m[i]){
            d.push_back({m[i], i});
        }
        sum += m[i];
    }
    ans = max(ans, sum);
    for(int i = 1; i < n; i++){
        int prev = arr[i - 1], j = i + n - 1, r = j - 1, l;
        while(!d.empty() and d.back().first > prev){
            auto [val, id] = d.back();
            d.pop_back();
            l = id;
            sum -= (r - l + 1) * val;
            r = l - 1;
        }
        d.push_back({prev, l});
        d.push_back({n, j});
        sum += (j - l) * prev;
        sum += n;
        ans = max(ans, sum);
    }
    cout << ans << endl;
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