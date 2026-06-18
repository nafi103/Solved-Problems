#include<bits/stdc++.h>
using namespace std;
 void solution(){
    int w,d,h,a,b,f,g;
    cin >> w >> d >> h >> a >> b >>f >> g;
    int ans1 = (h+b+g+abs(a-f)), ans2 = (h+abs(a-f)+(d-b)+(d-g));
    int ans3 = h+abs(b-g)+(w-a)+(w-f) , ans4 = h+a+f+abs(b-g);
    cout<<min(min(ans1,ans2),min(ans3,ans4))<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--){
        solution();
    }
}