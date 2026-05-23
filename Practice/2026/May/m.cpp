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
    vector<int> arr(n), id(n + 1, 0);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        id[arr[i]] = i;
    }
    deque<int> d;
    vector<int> ans;
    for(int i = 1; i <= n; i++){
        d.push_front(i);
        int cnt = 0;
        while(id[d.front()] == id[d.back()] + 1){
            int x = d.front();
            d.pop_front();
            cnt++;
            d.push_back(x);
        }
        if(cnt == 0){
            ans.push_back(i);
        }else{
            ans.push_back(cnt);
        }
    }
    for(auto &x: ans)
        cout << x << " ";
    cout << endl;
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