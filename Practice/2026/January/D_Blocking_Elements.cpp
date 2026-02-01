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

const int N = 1e5 + 10;
int n, a[N], dp[N], pref[N];

void input(){
    cin >> n;
    for(int i = 1; i <= n; i++){
        cin >> a[i];
        pref[i] = pref[i - 1] + a[i];
    }
}

bool check(int mx){
    set<pair<int,int>> ms = {{0, 0}};
    int l = 0;
    for(int r = 1; r <= n; r++){
        while(pref[r - 1] - pref[l] > mx){
            ms.erase({dp[l], l});
            l++;
        }
        dp[r] = a[r] + (*ms.begin()).first;
        ms.insert({dp[r], r});
    }
    for(int i = n, sum = 0; i >= 0 and sum <= mx; sum += a[i], i--){
        if(dp[i] <= mx)
            return true;
    }
    return false;
}

int bs(int l, int r){
    if(l > r)
        return l;
    int mid = (l + r) / 2;
    if(check(mid))
        return bs(l, mid - 1);
    return bs(mid + 1, r);
}

void solve()
{
    input();
    cout << bs(1, pref[n]) << endl;
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