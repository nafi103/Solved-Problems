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
int n, m, a[N];
 bool not_possible(){
    int g = a[0];
    for(int i = 1; i < n; i++){
        g = gcd(g, a[i]);
        if(g != a[i])
            return true;
    }
    return false;
}
 void input(){
    cin >> n >> m;
    for(int i = 0; i < n; i++)
        cin >> a[i];
}
 vector<int> get_prime_factors(int x){
    vector<int> prime_factors;
    for(int i = 2; i * i <= x; i++){
        if(x % i == 0){
            prime_factors.push_back(i);
            while(x % i == 0)
                x /= i;
        }
    }
    if(x > 1)
        prime_factors.push_back(x);
    return prime_factors;
}
 int not_coprime(int x, int n){
    if(x == 1)
        return 0;
    vector<int> prime_factors = get_prime_factors(x);
    int r = (1 << sz(prime_factors)), len = sz(prime_factors), ans = 0;
    for(int i = 1; i < r; i++){
        int val = 1, cnt = 0;
        for(int j = 0; j < len; j++){
            if((1 << j) & i){
                cnt++;
                val *= prime_factors[j];
            }
        }
        if(cnt & 1){
            ans += n/val;
        }else{
            ans -= n/val;
        }
    }
    return ans;
}
 void solve()
{
    input();
    if(not_possible()){
        cout << 0 << endl;
        return;
    }
    int ans = 1, g = a[0];
    for(int i = 1; i < n; i++){
        int new_g = gcd(g, a[i]), exclude = g / new_g, coprimes = m / new_g - not_coprime(exclude, m / new_g);
        ans = (ans * coprimes) % mod;
        g = new_g;
    }
    cout << ans << endl;
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