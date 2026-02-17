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
    string str;
    cin >> str;
    map<int,int> mp;
    stack<int> st;
    int n = sz(str), valid[n];
    for(int j = 0; j < n; j++){
        if(str[j] == '('){
            st.push(j);
            valid[j] = 0;
        }else if(!st.empty()){
            int i = st.top();
            st.pop();
            int len = j - i + 1;
            if(i)
                len += valid[i - 1];
            mp[len]++;
            valid[j] = len;
        }else{
            valid[j] = 0;
        }
    }
    if(mp.empty()){
        cout << "0 1" << endl;
    }else{
        auto [f, s] = *mp.rbegin();
        cout << f << " " << s << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}