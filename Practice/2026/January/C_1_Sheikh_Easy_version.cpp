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

const int N = 2e5 + 10;
int arr[N], pref[N], pxor[N], n, q, a, b;

void input(){
    cin >> n >> q;
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        pref[i] = arr[i] + pref[i - 1];
        pxor[i] = arr[i] ^ pxor[i - 1];
    }
    cin >> a >> b;
}

int f(int l, int r){
    l = max(l, 1ll);
    return pref[r] - pref[l - 1] - (pxor[r] ^ pxor[l - 1]);
}

void solve()
{
    input();
    int l = a, target = f(a, b);
    int len = b - a + 1, ansl = a, ansr = b;
    for(int r = a; r <= b; r++){
        while(l <= r and f(l, r) >= target){
            l++;
        }
        if(f(l - 1, r) == target and len > r - l + 2){
            len = r - l + 2;
            ansl = l - 1;
            ansr = r;
        }
    }
    cout << ansl << ' ' << ansr << endl;
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