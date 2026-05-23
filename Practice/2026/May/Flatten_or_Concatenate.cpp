#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

int query(int l, int r){
    cout << "? " << l << " " << r << endl;
    int x;
    cin >> x;
    return x;
}

void solve()
{
    int n;
    cin >> n;
    int L = 1, R = n;
    while(L < R){
        int l = L, r = R;
        while(l < r){
            int mid = (l + r) / 2;
            int left_sum = query(L, mid);
            int right_sum = query(mid + 1, R);
            if(left_sum == right_sum){
                l = mid;
                break;
            }
            if(left_sum < right_sum)
                l = mid + 1;
            else
                r = mid - 1;
        }
        if((l - L + 1) < (R - l))
            R = l;
        else
            L = l + 1;
    }
    int mx = query(L, L);
    cout << "! " << mx << endl;
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