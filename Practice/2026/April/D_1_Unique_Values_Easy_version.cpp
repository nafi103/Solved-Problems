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

map<pair<int,int>,int> save;

int query(int l, int r){
    if(save.count({l, r}))
        return save[{l, r}];
    if(l == r)
        return 1;
    cout << "? " << (r - l + 1);
    for (int i = l; i <= r; i++){
        cout << " " << i;
    }
    cout << endl;
    int x;
    cin >> x;
    save[{l, r}] = x;
    return x;
}

int query(int l, int r, int extra){
    cout << "? " << (r - l + 2);
    for (int i = l; i <= r; i++){
        cout << " " << i;
    }
    cout << " " << extra;
    cout << endl;
    int x;
    cin >> x;
    save[{l, r}] = x;
    return x;
}

void solve()
{
    save.clear();
    int n;
    cin >> n;
    save[{1, 2 * n + 1}] = 0;
    int R, L;
    int l = 3, r = 2 * n + 1;
    while(l <= r){
        int mid = (l + r) / 2;
        int x = query(1, mid);
        int rem = (mid - x);
        if(rem & 1){
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }
    R = l;
    l = 1;
    r = R - 2;
    while(l <= r){
        int mid = (l + r) / 2;
        int x = query(mid, R);
        int rem = (R - mid + 1 - x);
        if(rem & 1){
            l = mid + 1;
        }else{
            r = mid - 1;
        }
    }
    L = r;
    l = L + 1;
    r = R - 1;
    while(l <= r){
        int mid = (l + r) / 2;
        int x = query(L, mid, R);
        int rem = (mid - L + 2) - x;
        if(rem & 1){
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }
    cout << "! " << L << " " << l << " " << R << endl;
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