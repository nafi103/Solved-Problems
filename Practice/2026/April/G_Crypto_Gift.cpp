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
int n, x, y, diff;
vector<int> arr;

bool check(int times){
    int rem_y = times, need = 0;
    for(int i = 1; i <= n; i++){
        int val = arr[i];
        if(times * x >= val)
            continue;
        need += (val - (times * x) + diff - 1) / diff;
    }
    return need <= times;
}


void solve()
{
    int mx = -inf;
    cin >> n;
    arr.resize(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        mx = max(mx, arr[i]);
    }
    cin >> x >> y;
    if(x >= y or x >= mx){
        cout << (mx + x - 1) / x << endl;
        return;
    }
    diff = y - x;
    int l = 1, r = 1e9;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(mid))
            r = mid - 1;
        else
            l = mid + 1;
    }
    cout << l << endl;
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