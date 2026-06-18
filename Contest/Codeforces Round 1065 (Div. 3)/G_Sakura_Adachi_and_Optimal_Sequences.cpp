#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e6 + 3;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
const int N = mod + 10;
int n,fact[N];
 int expo(int a, int b, int m) {int res = 1; while (b > 0) {if (b & 1)res = (res * a) % m; a = (a * a) % m; b = b >> 1;} return res;}
 int mminvprime(int a) {return expo(a, mod - 2, mod);}
 int go(int a, int b){
    int res = 0;
    while((a<<1) <= b){
        a<<=1;
        res++;
    }
    return res;
}
 void solve()
{
    int operation = 0, way = 1;
    cin >> n;
    vector<int> a(n), b(n);
    for(auto &x: a)
        cin >> x;
    for(auto &x: b)
        cin >> x;
    int mult = inf;
    for(int i = 0; i < n; i++){
        if(a[i] == b[i]){
            mult = 0;
            break;
        }
        mult = min(mult,go(a[i], b[i]));
    }
    vector<vector<int>> steps;
    for(int i = 0; i < n; i++){
        vector<int> tmp;
        int y = b[i], x = a[i], rem = mult;
        while(rem--){
            if(y&1)
                tmp.push_back(1);
            else 
                tmp.push_back(0);
            y >>= 1;
        }
        tmp.push_back(y-x);
        operation += accumulate(all(tmp),0ll);
        steps.push_back(tmp);
    }
    operation += mult;
    for(int j = 0; j <= mult; j++){
        int this_step = 0;
        for(int i = 0; i < n; i++){
            this_step += steps[i][j];
        }
        if(this_step >= mod){
            way = 0;
            break;
        }
        int p = fact[this_step];
        for(int i = 0; i < n; i++){
            p = (p * mminvprime(fact[steps[i][j]])) % mod;
        }
        way = (way * p) % mod;
    }
    cout << operation <<" " << way << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    fact[0] = 1;
    for(int i = 1; i < N; i++){
        fact[i] = (fact[i - 1] * i) % mod;
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}