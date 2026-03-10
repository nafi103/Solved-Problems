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
    int n;
    cin >> n;
    stack<pair<int,int>>st;
    for(int i = 0, sum; i < n; i++){
        cin >> sum;
        int cnt = 1;
        while(!st.empty() and st.top().first >= sum / cnt){
            sum += st.top().first * st.top().second;
            cnt += st.top().second;
            st.pop();
        }
        st.push({sum / cnt, cnt - sum % cnt});
        if(sum % cnt)
            st.push({sum / cnt + 1, sum % cnt});
    }
    int mx = st.top().first;
    while(sz(st) > 1)
        st.pop();
    cout << mx - st.top().first << endl;
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