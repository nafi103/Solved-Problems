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
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
int getRandomNumber(int l, int r) {return uniform_int_distribution<int>(l, r)(rng);}
 int mx = 0;
 int gcd(int a, int b, int& x, int& y) {
    if (b == 0) {
        x = 1;
        y = 0;
        return a;
    }
    int x1, y1;
    int d = gcd(b, a % b, x1, y1);
    x = y1;
    y = x1 - y1 * (a / b);
    return d;
}
 bool find_any_solution(int a, int b, int c, int &x0, int &y0, int &g) {
    g = gcd(abs(a), abs(b), x0, y0);
    if (c % g) {
        return false;
    }
     x0 *= c / g;
    y0 *= c / g;
    if (a < 0) x0 = -x0;
    if (b < 0) y0 = -y0;
    return true;
}
 struct Operation{
    int a, b;
    char op;
     Operation(){}
     Operation(int _a, int _b, char _op) : a(_a), b(_b), op(_op) {}
     void show(){
        cout << a << " " << op << " " << b << endl;
    }
};
 int msb(int n){
    return 63ll - __builtin_clzll(n);
}
 void solve()
{
    int n;
    cin >> n;
    int cn = -1;
    vector<Operation> op;
    op.push_back({n, n, '+'});
    set<int> s = {n, 2 * n};
    vector<int> arr = {n, 2 * n};
    for (int i = 0; i < 100000; i++){
        int x1 = getRandomNumber(0, sz(arr) - 1), x2 = getRandomNumber(0, sz(arr) - 1);
        // debug(x1) debug(x2)
        int num1 = arr[x1] + arr[x2], num2 = (arr[x1] ^ arr[x2]);
        // debug(num1) debug(num2)
        if(s.count(num1) == 0){
            op.push_back(Operation(arr[x1], arr[x2], '+'));
            int g = gcd(num1, n);
            s.insert(num1);
            arr.push_back(num1);
            if(g == 1){
                cn = num1;
                mx = max(mx, i * 2 + 1);
                break;
            }
        }
        if(num2 and s.count(num2) == 0){
            op.push_back(Operation(arr[x1], arr[x2], '^'));
            int g = gcd(num2, n);
            s.insert(num2);
            arr.push_back(num2);
            if(g == 1){
                mx = max(mx, i * 2 + 2);
                cn = num2;
                break;
            }
        }
    }
    // debug(s)
    // debug(cn)
    if(cn == -1){
        cout << n << endl;
    }
    // debug(s)
    // debug(cn)
    int a = n, b = cn, c = 1, x, y, g = 1;
    find_any_solution(a, b, c, x, y, g);
    if (y > 0) {
        int k = (y + a - 1) / a; 
        y -= k * a;
        x += k * b;
    } else {
        int k = (-y) / a;
        y += k * a;
        x -= k * b;
    }
     if (abs(b * y) % 2 != 0) {
        y -= a;
        x += b;
    }
    x = abs(x), y = abs(y);
    int n1 = a * x, n2 = b * y;
     int prev = a;
    while(prev <= n1){
        op.push_back(Operation(prev, prev, '+'));
        prev += prev;
    }
    prev >>= 1;
    int p = msb(x) - 1, curra = prev;
    while(p >= 0){
        if(x & (1ll << p)){
            int need = (1ll << p) * a;
            op.push_back(Operation(curra, need, '+'));
            curra += need;
        }
        p--;
    }
     prev = b;
    while(prev <= n2){
        op.push_back(Operation(prev, prev, '+'));
        prev += prev;
    }
    prev >>= 1;
    p = msb(y) - 1;
    int currb = prev;
    while(p >= 0){
        if(y & (1ll << p)){
            int need = (1ll << p) * b;
            op.push_back(Operation(currb, need, '+'));
            currb += need;
        }
        p--;
    }
     op.push_back(Operation(curra, currb, '^'));
    cout << sz(op) << endl;
    for(auto &o: op)
        o.show();
    // set<int> newS = {n};
    // for(auto &o: op){
    //     int l = o.a, r = o.b;
    //     if(newS.count(l) and newS.count(r)){
     //     }else{
    //         for(auto &val: newS){
    //             cout << val << " ";
    //         }
    //         cout << endl;
    //         cout << l << " " << r << endl;
    //         break;
    //     }
    //     if(o.op == '+'){
    //         newS.insert(l + r);
    //     }else{
    //         newS.insert(l ^ r);
    //     }
    // }
    // debug(newS)
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // for (int z = 3; z <= 99999; z += 2)
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}