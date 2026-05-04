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
    vector<int> arr(n + 2), left(n + 2), right(n + 2);
    left[0] = right[0] = left[n + 1] = right[n + 1] = 0;
    arr[0] = arr[n + 1] = -5;
    set<pair<int,int>> s;
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        left[i] = i - 1;
        right[i] = i + 1;
    }
    for(int i = 1; i <= n; i++){
        if((arr[i] == arr[i - 1] + 1) or (arr[i] == arr[i + 1] + 1)){
            s.insert({arr[i], i});
        }
    }
    int last = inf;
    int rem = n - 1;
    while(!s.empty()){
        auto [val, node] = *s.rbegin();
        s.erase({val, node});
        last = val;
        rem--;
        int l = left[node], r = right[node];
        right[l] = r;
        left[r] = l;
        if(arr[r] == arr[l] + 1){
            s.insert({arr[r], r});
        }
        if(arr[l] == arr[r] + 1){
            s.insert({arr[l], l});
        }
    }
    if(rem == 0 and last == 1){
        cout << "YES" << endl;
    }else{
        cout << "NO" << endl;
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