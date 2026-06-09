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

const int N = 3e5 + 10;
int n, arr[N], forbid[N];

void solve()
{
    int ans = 0;
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        forbid[i] = -1;
    }
    stack<pair<int,int>> st;
    for(int i = n - 1; i >= 0; i--){
        auto &x = arr[i];
        while(!st.empty() and st.top().first == x + 1){
            auto [_, id] = st.top();
            st.pop();
            forbid[id] = i;
        }
        st.push({x, i});
    }
    for(int i = 0; i < n; i++){
        int left = i - forbid[i], right = (n - i);
        ans += left * right;
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